import InitECandidate.Runtime.NodedbBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The complete database-builder budget is monotone in the decoded entry
count, including the collision/growth contribution of its hash table. -/
theorem nodedb_body_cost_mono (a b : BitVec 64) (ordered : a.toNat ≤ b.toNat) :
    nodedbBodyCost a ≤ nodedbBodyCost b := by
  have setCost := setBodyCost_mono 32 (536870912#64) (536870912#64) a b
    (le_refl _) ordered (by decide)
  have iter : nodedbIterationCost (536870912#64) a ≤ nodedbIterationCost (536870912#64) b := by
    unfold nodedbIterationCost
    omega
  have product := Nat.mul_le_mul ordered (Nat.add_le_add_right iter 1)
  unfold nodedbBodyCost nodedbTailCost
  omega

/-- Input-dependent call budget for either database builder. Decoding bounds
the entry count by one quarter of the input length. -/
def nodedbInputCallCost (inputLimit : Nat) : Nat :=
  nodedbBodyCost (BitVec.ofNat 64 (inputLimit / 4)) + 1

theorem nodedb_call_cost_le_input (count inputLength : BitVec 64) (inputLimit : Nat)
    (countBound : count.toNat ≤ inputLength.toNat / 4)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712) :
    nodedbBodyCost count + 1 ≤ nodedbInputCallCost inputLimit := by
  have countLimit : count.toNat ≤ inputLimit / 4 :=
    countBound.trans (Nat.div_le_div_right inputBound)
  have cast : (BitVec.ofNat 64 (inputLimit / 4)).toNat = inputLimit / 4 :=
    Nat.mod_eq_of_lt (by omega)
  have cost := nodedb_body_cost_mono count (BitVec.ofNat 64 (inputLimit / 4)) (by rw [cast]; exact countLimit)
  unfold nodedbInputCallCost
  omega

#print axioms nodedb_body_cost_mono
#print axioms nodedb_call_cost_le_input
end InitECandidate.Runtime
