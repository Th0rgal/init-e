import InitECandidate.Runtime.UdivmodSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Remainder candidate of the actual iteration with Nat shift amounts. -/
def udivmodR1 (a r i : BitVec 64) : BitVec 64 := r <<< (1 : Nat) ||| ((a >>> (i - 1).toNat) &&& 1)

/-- Locals after one actual iteration. -/
def udivmodStepState {σ : Type} (state : PanSemStateFiniteExact 64 σ) (a b q r i : BitVec 64) :
    PanSemStateFiniteExact 64 σ :=
  let s1 := setVarHOLFinite (ofString "i") (.val (.word (i - 1))) state
  let s2 := setVarHOLFinite (ofString "r") (.val (.word (udivmodR1 a r i))) s1
  if udivmodR1 a r i < b then s2
  else setVarHOLFinite (ofString "q") (.val (.word (q ||| (1 <<< (i - 1).toNat))))
    (setVarHOLFinite (ofString "r") (.val (.word (udivmodR1 a r i - b))) s2)

theorem evaluate_udivmodStep {σ : Type} (state : PanSemStateFiniteExact 64 σ) (a b q r i : BitVec 64)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hq : state.locals.lookup (ofString "q") = some (.val (.word q)))
    (hr : state.locals.lookup (ofString "r") = some (.val (.word r)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i)))
    (nz : i ≠ 0) (bound : i.toNat ≤ 64) :
    evaluateHOLFiniteState state udivmodStep = (none, udivmodStepState state a b q r i) := by
  classical
  have small : (i - 1).toNat < 64 := by
    have : i.toNat ≠ 0 := fun h => nz (BitVec.eq_of_toNat_eq (by simp [h]))
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega
  have small' : ¬ (64 ≤ (i - 1#64).toNat) := by
    have : (i - 1#64) = i - 1 := rfl
    rw [this]; omega
  have hor : ∀ x y : BitVec 64, OrOp.or x y = x ||| y := fun _ _ => rfl
  have hand : ∀ x y : BitVec 64, AndOp.and x y = x &&& y := fun _ _ => rfl
  have hone : (1#64 &&& 18446744073709551615#64 : BitVec 64) = 1#64 := by decide
  have d1 : ofString "i" ≠ ofString "a" := by decide_cbv
  have d2 : ofString "i" ≠ ofString "b" := by decide_cbv
  have d3 : ofString "i" ≠ ofString "q" := by decide_cbv
  have d4 : ofString "i" ≠ ofString "r" := by decide_cbv
  have d5 : ofString "r" ≠ ofString "a" := by decide_cbv
  have d6 : ofString "r" ≠ ofString "b" := by decide_cbv
  have d7 : ofString "r" ≠ ofString "q" := by decide_cbv
  have d8 : ofString "q" ≠ ofString "i" := by decide_cbv
  unfold udivmodStep udivmodStepState udivmodR1
  simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_ite,
    evalHOLExact, evalListHOLExact, toExact, lookupKvarHOLExact, isValidValueHOLExact, shapeOfHOLExact,
    shapeEqHOL, setKvarHOLFinite, setVarHOLFinite, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL,
    HolFiniteMapExact.lookup_update, FUPDATE, ha, hb, hq, hr, hi, d1, d2, d3, d4, d5, d6, d7, d8,
    Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, Ne.symm d7, Ne.symm d8,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, small', hor, hand, hone, BitVec.or_zero, -BitVec.toNat_sub]
  split <;> rfl

#print axioms evaluate_udivmodStep
end InitECandidate.Runtime
