import InitECandidate.Runtime.PayloadOffsetCheckReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The four accepted payload offsets form ordered, nonwrapping input spans. -/
theorem payload_offset_bounds {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offsets length extra transactions withdrawals balance : BitVec 64)
    (first : memWord state.memory offsets = 540)
    (accepted : ∀ k : BitVec 64, k.toNat < 4 → SszOffsetOK state offsets 540 length k)
    (readExtra : memWord state.memory offsets = extra)
    (readTransactions : memWord state.memory (offsets + 8) = transactions)
    (readWithdrawals : memWord state.memory (offsets + 16) = withdrawals)
    (readBalance : memWord state.memory (offsets + 24) = balance) :
    extra = 540 ∧ 540 ≤ transactions.toNat ∧ transactions.toNat ≤ withdrawals.toNat ∧
      withdrawals.toNat ≤ balance.toNat ∧ balance.toNat ≤ length.toNat := by
  have one := accepted 1 (by decide)
  have two := accepted 2 (by decide)
  have three := accepted 3 (by decide)
  have previousTwo : offsets + (2 : BitVec 64) * 8 - 8 = offsets + 8 := by
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have previousThree : offsets + (3 : BitVec 64) * 8 - 8 = offsets + 16 := by
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have positiveTwo : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess (0 : BitVec 64) 2 = true := by decide
  have positiveThree : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess (0 : BitVec 64) 3 = true := by decide
  have txLower := one.2.1
  have wdOrder := (two.2.2.2 positiveTwo).2
  have balOrder := (three.2.2.2 positiveThree).2
  have balUpper := three.2.2.1
  change ¬ memWord state.memory (offsets + 8) < (540 : BitVec 64) at txLower
  change ¬ memWord state.memory (offsets + 16) < memWord state.memory (offsets + 16 - 8) at wdOrder
  change ¬ memWord state.memory (offsets + 24) < memWord state.memory (offsets + 24 - 8) at balOrder
  change ¬ length < memWord state.memory (offsets + 24) at balUpper
  rw [readTransactions] at txLower
  rw [show offsets + 16 - 8 = offsets + 8 from previousTwo,readTransactions,readWithdrawals] at wdOrder
  rw [show offsets + 24 - 8 = offsets + 16 from previousThree,readWithdrawals,readBalance] at balOrder
  rw [readBalance] at balUpper
  refine ⟨readExtra.symm.trans first,?_,?_,?_,?_⟩
  · change ¬ transactions.toNat < 540 at txLower
    omega
  · change ¬ withdrawals.toNat < transactions.toNat at wdOrder
    omega
  · change ¬ balance.toNat < withdrawals.toNat at balOrder
    omega
  · change ¬ length.toNat < balance.toNat at balUpper
    omega

#print axioms payload_offset_bounds
end InitECandidate.Runtime
