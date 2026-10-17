import InitECandidate.Runtime.RollbackWorldDeleteCall
import InitECandidate.Runtime.RollbackDeletePhysicalFootprints
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion retains both the complete world and the separation needed
by the next journal iteration. -/
theorem RollbackWorld.delete_call_preserves_separation {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧
      RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock := by
  have separation : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address := by
    intro other member different op ok os oc ou ov oo oop oi ob otherReady address targetMember otherMember
    exact separated table registered other member (Ne.symm different) address
      ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits address).mpr targetMember)
      ((otherReady.rollback_footprint_iff state widths other op ok os oc ou ov oo oop oi ob address).mpr otherMember)
  obtain ⟨post,run,preserved,cost,remaining⟩ := RollbackWorld.delete_call_preserves state widths tables
    table pointer keys stride capacity used values order orderPos items key bits supported ready strideBound large
    tableArgument keyArgument args keyAligned words bytes budget journal snapshot count world registered separation
  obtain ⟨checked,checkedRun,subset,_,_⟩ := rollback_delete_physical_footprint_subset state widths tables
    table pointer keys stride capacity used values order orderPos items key bits supported ready strideBound large
    tableArgument keyArgument args keyAligned words bytes budget world.ready separation
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at subset
  exact ⟨post,run,preserved,separated.of_footprint_subset subset,cost,remaining⟩

#print axioms RollbackWorld.delete_call_preserves_separation
end InitECandidate.Runtime
