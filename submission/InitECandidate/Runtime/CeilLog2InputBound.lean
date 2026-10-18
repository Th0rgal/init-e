import InitECandidate.Runtime.CeilLog2Small
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem shift_one_toNat_of_lt64 (d : BitVec 64) (small : d.toNat < 64) :
    ((1#64) <<< d.toNat).toNat = 2 ^ d.toNat := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  have bound : 2 ^ d.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) small
  simpa using Nat.mod_eq_of_lt bound

/-- The challenge's checked input limit caps the actual helper result at 27,
and its power-of-two buffer covers the requested chunk count without wrapping. -/
theorem ceilLog2_body_input_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (value : ValueHOL 64)
    (input : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "n") = some (.val (.word n)))
    (small : n.toNat ≤ 134217712)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ceil_log2) =
      (some (.returned value),post)) :
    ∃ d : BitVec 64, value = .val (.word d) ∧ d.toNat ≤ 27 ∧
      n.toNat ≤ ((1#64) <<< d.toNat).toNat ∧
      ((1#64) <<< d.toNat).toNat ≤ 134217728 := by
  obtain ⟨d,bounded,valueEq⟩ := ceilLog2_body_returned_small state post n value 27
    (by decide) (by change n.toNat ≤ 134217728; omega) input run
  obtain ⟨other,_,otherEq,covers⟩ := ceilLog2_body_returned state post n value input run
  have equal : other = d := by cases valueEq.symm.trans otherEq; rfl
  subst other
  refine ⟨d,valueEq,bounded,covers,?_⟩
  rw [shift_one_toNat_of_lt64 d (by omega)]
  have upper : 2 ^ d.toNat ≤ 2 ^ 27 := Nat.pow_le_pow_right (by decide) bounded
  exact upper

#print axioms shift_one_toNat_of_lt64
#print axioms ceilLog2_body_input_bound
end InitECandidate.Runtime
