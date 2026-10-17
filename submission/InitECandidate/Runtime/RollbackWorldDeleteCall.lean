import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.RollbackDeletePhysicalTableFamily
import InitECandidate.Runtime.HashTableDeleteCallRecordFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual delete call retains typed records, referenced identities, the
entire table registry and rollback metadata under physical table separation. -/
theorem RollbackWorld.delete_call_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat)
    (tableArgument keyArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat * 57 + 3 ≤ state.clock)
    (journal snapshot count : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (registered : table ∈ tables)
    (separated : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock := by
  obtain ⟨post,run,family,cost,remaining⟩ := rollback_delete_physical_table_family state widths tables
    table pointer keys stride capacity used values order orderPos items key bits supported ready strideBound large
    tableArgument keyArgument args keyAligned words bytes budget world.ready separated
  have journalBefore := world.layout table registered
  have journalBound : journal.toNat + count.toNat * 32 ≤ 33806089496 := by
    have hk := ready.live.arrays.headerKeys
    have ku := ready.live.arrays.keysBefore
    have uo := ready.live.arrays.usedBefore
    have oo := ready.live.arrays.orderBefore
    have bounded := ready.live.arrays.endBound
    omega
  obtain ⟨checked,checkedRun,_,frame,_,_,locals,globals,_,domain,_⟩ :=
    ready.delete_call_supported_with_record_frame state (widths table) table pointer keys stride capacity used values order orderPos items key bits supported
      tableArgument keyArgument args keyAligned words bytes budget journal count.toNat journalBound (Or.inr journalBefore)
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at frame locals globals domain
  have preserved := world.after_frame (next := count) (after := post) (Nat.le_refl _)
    (by rw [globals]; exact world.counter)
    (by rw [locals]; exact world.snapshotLocal)
    (by rw [globals]; exact world.journalGlobal) domain frame family
  exact ⟨post,run,preserved,cost,remaining⟩

#print axioms RollbackWorld.delete_call_preserves
end InitECandidate.Runtime
