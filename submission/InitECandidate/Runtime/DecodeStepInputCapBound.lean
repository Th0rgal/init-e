import InitECandidate.Runtime.DecodeStepUniformBodyBound
namespace InitECandidate.Runtime

theorem decodeStepTwoCaseCost_mono (n m : Nat) (h : n ≤ m) :
    decodeStepTwoCaseCost n ≤ decodeStepTwoCaseCost m := by
  have product : n*((2*n+1)*15+19) ≤ m*((2*m+1)*15+19) := Nat.mul_le_mul h (by omega)
  have divided : n/4 ≤ m/4 := Nat.div_le_div_right h
  exact Nat.add_le_add (Nat.add_le_add_right product 92633)
    (Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right divided 7)
      (Nat.add_le_add_right product 92637)) 1)

theorem decodeStepBodyCost_mono (n m : Nat) (h : n ≤ m) : decodeStepBodyCost n ≤ decodeStepBodyCost m :=
  Nat.add_le_add (decodeStepParseCost_mono n m h)
    (Nat.add_le_add (decodeStepSlicesCost_mono n m h) (decodeStepTwoCaseCost_mono n m h))

/-- A fixed numerical ceiling for one complete original decoder call at the
challenge's accessible-input limit. This is not the whole traversal bound. -/
theorem decodeStepBodyCost_at_input_cap : decodeStepBodyCost 134217712 = 2161727325639847002 := by decide

theorem decodeStepBodyCost_input_cap (length : Nat) (bounded : length ≤ 134217712) :
    decodeStepBodyCost length ≤ 2161727325639847002 := by
  rw [← decodeStepBodyCost_at_input_cap]
  exact decodeStepBodyCost_mono length 134217712 bounded

#print axioms decodeStepTwoCaseCost_mono
#print axioms decodeStepBodyCost_mono
#print axioms decodeStepBodyCost_at_input_cap
#print axioms decodeStepBodyCost_input_cap
end InitECandidate.Runtime
