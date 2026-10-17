import InitECandidate.Runtime.HashTableSetCallAllPlansOtherValuesIn
import InitECandidate.Runtime.HashTableValuesInSetCallAllPlans
import InitECandidate.Runtime.RollbackWorldRegisteredSet
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual normal set calls preserve every watched pointer table, including
the modified table when its new value is registered. Numeric tables impose no
new-value membership requirement. -/
theorem RollbackWorld.registered_set_values_in_family {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 74 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (newMember : table ∈ watched → value ∈ targets)
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    ∀ other ∈ watched, HashTableValuesIn other targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have headerBefore : table.toNat + 72 ≤ pointer.toNat := by
    have := ready.live.arrays.headerKeys
    have := ready.live.arrays.keysBefore
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.frontier.allocated
    omega
  have domain : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) →
      ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address := by
    intro safePlan address lower upper
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,limit⟩ := htabGrow_array_layout_from_safe_plan table pointer capacity stride small ready.live.frontier.aligned headerBefore ready.live.frontier.bounded capacityBound safePlan
    exact heapDomain address (by omega)
  intro other belongs
  by_cases same : other = table
  · subst other
    have outcome := ready.set_call_all_plans_values_in state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
      targets (registered table belongs) (newMember belongs) small ticks domain tableArgument keyArgument valueArgument args large aligned words bytes
    rcases outcome with good | failure
    · obtain ⟨post,run,_,postRegistered,_⟩ := good
      rw [run]
      exact postRegistered
    · exact False.elim (failure.1 success)
  · obtain ⟨op,ok,os,oc,ou,ov,oo,orev,oi,ob,otherReady,_,_⟩ := world.ready other (watchedSubset belongs)
    have frontier : op = pointer := by
      have equal := otherReady.live.frontier.heap.symm.trans ready.live.frontier.heap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    subst op
    have apart : ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order reverse address →
        ¬tablePhysicalRegion other ok os oc ou ov oo orev address := by
      intro address targetMember otherMember
      exact separated table member other (watchedSubset belongs) (Ne.symm same) address
        ((ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order reverse items bits address).mpr targetMember)
        ((otherReady.rollback_footprint_iff state widths other pointer ok os oc ou ov oo orev oi ob address).mpr otherMember)
    exact ready.set_call_all_plans_other_values_in state (widths table) table pointer keys stride capacity used values order reverse items key value bits supported
      (widths other) other ok os oc ou ov oo orev oi ob otherReady targets (registered other belongs) apart small ticks domain
      tableArgument keyArgument valueArgument args large aligned words bytes success

#print axioms RollbackWorld.registered_set_values_in_family
end InitECandidate.Runtime
