import InitECandidate.Runtime.SszCheckOffsetsCallReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Accepted witness offset-table cells give the concrete ordering needed
by the three-list input-length bound. -/
theorem stateless_witness_offset_bounds {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offsets length first middle last : BitVec 64)
    (firstChecked : memWord state.memory offsets = 12)
    (accepted : ∀ k : BitVec 64, k.toNat < 3 → SszOffsetOK state offsets 12 length k)
    (readFirst : memWord state.memory offsets = first)
    (readMiddle : memWord state.memory (offsets + 8) = middle)
    (readLast : memWord state.memory (offsets + 16) = last) :
    first = 12 ∧ 12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ length.toNat := by
  have one := accepted 1 (by decide)
  have two := accepted 2 (by decide)
  have previous : offsets + (2 : BitVec 64) * 8 - 8 = offsets + 8 := by
    simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have positive : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess (0 : BitVec 64) 2 = true := by decide
  have lower := one.2.1
  have ordered := (two.2.2.2 positive).2
  have upper := two.2.2.1
  change ¬ memWord state.memory (offsets + 8) < (12 : BitVec 64) at lower
  change ¬ memWord state.memory (offsets + 16) < memWord state.memory (offsets + 16 - 8) at ordered
  change ¬ length < memWord state.memory (offsets + 16) at upper
  rw [readMiddle] at lower
  rw [show offsets + 16 - 8 = offsets + 8 from previous,readMiddle,readLast] at ordered
  rw [readLast] at upper
  refine ⟨readFirst.symm.trans firstChecked,?_,?_,?_⟩
  · change ¬ middle.toNat < 12 at lower
    omega
  · change ¬ last.toNat < middle.toNat at ordered
    omega
  · change ¬ length.toNat < last.toNat at upper
    omega

#print axioms stateless_witness_offset_bounds
end InitECandidate.Runtime
