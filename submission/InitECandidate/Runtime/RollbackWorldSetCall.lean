import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.RollbackSetPhysicalTableFamily
import InitECandidate.Runtime.HashTableReadySetCallRecordFrameSupported
import InitECandidate.Runtime.HashTableReadySetCallHeapFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful actual set preserves the full rollback world, including typed
record contents and the fixed registry, while allowing heap growth. -/
theorem RollbackWorld.set_call_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (budget : 3 * capacity.toNat + 2 * (capacity * 2).toNat + (widths table).toNat + 13 + items.toNat * ((capacity * 2).toNat + (widths table).toNat + 4) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post := by
  obtain ⟨post,run,family⟩ := rollback_set_physical_table_family state widths tables
    table pointer keys stride capacity used values order orderPos items key value bits supported ready strideBound large
    safePlan budget domain tableArgument keyArgument valueArgument args keyAligned words bytes world.ready separated
  have beforeTable := world.layout table registered
  have hk := ready.live.arrays.headerKeys
  have hv := ready.live.arrays.headerValues
  have ku := ready.live.arrays.keysBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have bounded := ready.live.arrays.endBound
  have allocated := ready.live.frontier.allocated
  have capacityBound : capacity.toNat ≤ 33806089496 := by omega
  obtain ⟨checked,checkedRun,_,_,_,locals,_,addresses,_,frame⟩ :=
    ready.set_call_supported_record_frame state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan (by omega)
      ready.live.frontier.heap domain tableArgument keyArgument valueArgument args large keyAligned words bytes
      journal count.toNat (by omega) (by omega) (by omega) (Or.inl beforeTable)
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at locals addresses frame
  obtain ⟨framed,framedRun,_,_,_,_,_,_,_,globals,_⟩ :=
    ready.set_call_supported_heap_frame state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan (by omega)
      ready.live.frontier.heap domain tableArgument keyArgument valueArgument args large keyAligned words bytes
  have sameFrame : post = framed := congrArg Prod.snd (run.symm.trans framedRun)
  rw [← sameFrame] at globals
  have preserved := world.after_frame (next := count) (after := post) (Nat.le_refl _)
    ((globals (ofString "journal_n") (by decide)).trans world.counter)
    (by rw [locals]; exact world.snapshotLocal)
    ((globals (ofString "journal") (by decide)).trans world.journalGlobal) addresses frame family
  exact ⟨post,run,preserved⟩

#print axioms RollbackWorld.set_call_preserves
end InitECandidate.Runtime
