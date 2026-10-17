import InitECandidate.Runtime.RollbackWorldSetCall
import InitECandidate.Runtime.RollbackSetOtherPhysicalFootprints
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful set retains world and physical separation, even when arrays grow. -/
theorem RollbackWorld.set_call_preserves_separation {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (separated : RollbackPhysicalSeparated widths tables state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post := by
  have separation : ∀ other ∈ tables, other ≠ table → ∀ otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits,
      HashTableReady (widths other) other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state →
      ∀ address : BitVec 64,
        tablePhysicalRegion table keys stride capacity used values order orderPos address →
        ¬tablePhysicalRegion other otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address := by
    intro other member different op ok os oc ou ov oo oop oi ob otherReady address targetMember otherMember
    exact separated table registered other member (Ne.symm different) address
      ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order orderPos items bits address).mpr targetMember)
      ((otherReady.rollback_footprint_iff state widths other op ok os oc ou ov oo oop oi ob address).mpr otherMember)
  obtain ⟨post,run,preserved⟩ := RollbackWorld.set_call_preserves state widths tables
    table pointer keys stride capacity used values order orderPos items key value bits supported ready strideBound large
    safePlan budget domain tableArgument keyArgument valueArgument args keyAligned words bytes journal snapshot count world registered separation
  obtain ⟨checked,checkedRun,otherSubset⟩ := rollback_set_other_physical_footprints state widths tables
    table pointer keys stride capacity used values order orderPos items key value bits supported ready strideBound large
    safePlan budget domain tableArgument keyArgument valueArgument args keyAligned words bytes world.ready separation
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at otherSubset
  have targetSeparate : ∀ other ∈ tables, other ≠ table → ∀ address,
      rollbackTableFootprint widths table post address → ¬rollbackTableFootprint widths other post address := by
    intro other member different address targetInside otherInside
    obtain ⟨op,ok,os,oc,ou,ov,oo,oop,oi,ob,otherReady,_,_⟩ := world.ready other member
    have frontier : op = pointer := by
      have equal := otherReady.live.frontier.heap.symm.trans ready.live.frontier.heap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    subst op
    have apart := separation other member different pointer ok os oc ou ov oo oop oi ob otherReady
    obtain ⟨updated,updatedRun,cases,_⟩ := ready.set_call_supported_with_physical_table_safe_plan state (widths table) table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound safePlan budget domain large keyAligned words bytes
      (widths other) other ok os oc ou ov oo oop oi ob otherReady apart tableArgument keyArgument valueArgument args
    have equal : post = updated := congrArg Prod.snd (run.symm.trans updatedRun)
    rw [equal] at targetInside otherInside
    rcases cases with original | grown
    · obtain ⟨nextCount,_,targetReady,retained⟩ := original
      exact apart address
        ((targetReady.rollback_footprint_iff updated widths table pointer keys stride capacity used values order orderPos nextCount bits address).mp targetInside)
        ((retained.rollback_footprint_iff updated widths other pointer ok os oc ou ov oo oop oi ob address).mp otherInside)
    · have disjoint := grown.1.relocated_physical_separate state updated table pointer stride (capacity * 2)
        (htabGrowUsed pointer capacity stride) (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (widths table) _ (bits + 1)
        (widths other) other ok os oc ou ov oo oop oi ob otherReady
        (by intro location lower upper; exact apart location (Or.inl ⟨lower,upper⟩))
      exact disjoint address
        ((grown.1.rollback_footprint_iff updated widths table _ pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
          (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1) address).mp targetInside)
        ((grown.2.rollback_footprint_iff updated widths other _ ok os oc ou ov oo oop oi ob address).mp otherInside)
  refine ⟨post,run,preserved,?_⟩
  intro first firstMember second secondMember different address firstInside secondInside
  by_cases firstTarget : first = table
  · subst first
    exact targetSeparate second secondMember (Ne.symm different) address firstInside secondInside
  · by_cases secondTarget : second = table
    · subst second
      exact targetSeparate first firstMember firstTarget address secondInside firstInside
    · exact separated first firstMember second secondMember different address
        (otherSubset first firstMember firstTarget address firstInside)
        (otherSubset second secondMember secondTarget address secondInside)

#print axioms RollbackWorld.set_call_preserves_separation
end InitECandidate.Runtime
