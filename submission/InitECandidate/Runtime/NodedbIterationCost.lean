import InitECandidate.Runtime.NodedbInsertionNormalFrame
import InitECandidate.Runtime.HtabUnionInto
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A uniform iteration budget for the fixed-capacity node database. -/
def nodedbIterationCost (capacity total : BitVec 64) : Nat :=
  (134217712 * 20 + 125) + (setBodyCost 32 capacity total + 1)

theorem nodedb_iteration_cost_le (capacity total size count : BitVec 64)
    (small : size.toNat ≤ 134217712) (occupied : count.toNat ≤ total.toNat)
    (capacitySmall : capacity.toNat ≤ 536870912) :
    (size.toNat * 20 + 125) + (setBodyCost 32 capacity count + 1) ≤ nodedbIterationCost capacity total := by
  have mono := setBodyCost_mono 32 capacity capacity count total (le_refl _) occupied (by omega)
  unfold nodedbIterationCost
  omega

#print axioms nodedb_iteration_cost_le
end InitECandidate.Runtime
