import InitECandidate.Runtime.RollbackWorldSetAllPlans
import InitECandidate.Runtime.HashSetRegistryCostCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A registered set needs no caller-supplied table geometry or safe allocation
plan: success preserves the world, and allocation failure exits without timeout. -/
theorem RollbackWorld.registered_set_all_plans {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 72 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post) ∨
    (let result := (evaluateHOLFiniteState state (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1;
      result ≠ none ∧ result ≠ some .timeOut ∧ (∀ output : ValueHOL 64, result ≠ some (.returned output)) ∧ result ≠ some .continue) := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have ceiling := hashSetRegistryCost_le_ceiling capacity (widths table) items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
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
  rcases RollbackWorld.set_call_all_plans state widths tables table pointer keys stride capacity used values order reverse items key value bits supported ready small large
      (by change hashSetRegistryCost capacity (widths table) items ≤ state.clock; omega) domain tableArgument keyArgument valueArgument args aligned words bytes
      journal snapshot count world member separated with success | failure
  · exact Or.inl success
  · exact Or.inr ⟨failure.1,failure.2.1,failure.2.2.1,failure.2.2.2.1⟩

#print axioms RollbackWorld.registered_set_all_plans
end InitECandidate.Runtime
