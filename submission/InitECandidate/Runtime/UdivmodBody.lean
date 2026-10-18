import InitECandidate.Runtime.UdivmodTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual udivmod body for a nonzero divisor: at most 64 source clocks,
no timeout with 64 clocks, and every return is exactly <a / b, a % b>. -/
theorem evaluate_udivmod_body {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (ha : t.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) :
    let out := evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_udivmod)
    t.clock ≤ out.2.clock + 64 ∧ out.2.clock ≤ t.clock ∧ (64 ≤ t.clock → out.1 ≠ some .timeOut) ∧
      (∀ value, out.1 = some (.returned value) →
        value = .rStruct [.val (.word (a / b)), .val (.word (a % b))]) := by
  have nz' : ¬ b = 0#64 := nz
  rw [source_udivmod_body]
  by_cases lower : a < b
  · have q0 : a / b = 0#64 := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_udiv]; simp [Nat.div_eq_of_lt (BitVec.lt_def.mp lower)])
    have rA : a % b = a := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_umod]; exact Nat.mod_eq_of_lt (BitVec.lt_def.mp lower))
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
      evalHOLExact, evalListHOLExact, ha, hb, nz', lower, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite, q0, rA]
  · simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
      ha, hb, nz', lower, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, -evaluateHOLFiniteState_dec_total]
    exact evaluate_udivmodTail t a b ha hb nz

#print axioms evaluate_udivmod_body
end InitECandidate.Runtime
