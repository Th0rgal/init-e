import InitECandidate.Runtime.SszFixedListCountSource
import InitECandidate.Runtime.SszFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual ssz_fail call with a literal code: clock drops by at most one,
the result is terminal and never a normal return value. -/
theorem sszFail_literal_call {σ : Type} (c : PanSemStateFiniteExact 64 σ) (code : BitVec 64)
    (installed : c.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const code])
    c.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ c.clock ∧ (c.clock ≠ 0 → out.1 ≠ some .timeOut) ∧
      out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  have args : evalListHOLFinite c (h := fun address => Classical.propDecidable (c.memaddrs address))
      [.const code] = some [.val (.word code)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have lower := evaluateHOLFiniteState_clock_le c (.call (some (none,none)) (ofString "ssz_fail") [.const code])
  have terminal := evaluate_sszFail_call_terminal c (.const code) code installed args
  have noReturn := fun v => evaluate_sszFail_call_no_return c (.const code) code v installed args
  by_cases zero : c.clock = 0
  · exact ⟨by omega, lower, fun h => absurd zero h, terminal, noReturn⟩
  · have bounded := evaluate_sszFail_call_bounded c (.const code) code installed zero args
    exact ⟨by have := bounded.1; omega, lower, fun _ => bounded.2.1, terminal, noReturn⟩

theorem evaluate_sszFixedListCountTail {σ : Type} (c : PanSemStateFiniteExact 64 σ) (q r lim : BitVec 64)
    (installed : c.code = originalRuntimeCode)
    (hqr : c.locals.lookup (ofString "qr") = some (.rStruct [.val (.word q), .val (.word r)]))
    (hlim : c.locals.lookup (ofString "lim") = some (.val (.word lim))) :
    let out := evaluateHOLFiniteState c sszFixedListCountTail
    c.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ c.clock ∧ (c.clock ≠ 0 → out.1 ≠ some .timeOut) ∧
      out.1 ≠ none ∧ (∀ v, out.1 = some (.returned v) → v = .val (.word q) ∧ r = 0 ∧ ¬ lim < q) := by
  unfold sszFixedListCountTail
  by_cases nonzero : r = 0
  · by_cases over : lim < q
    · have fail := sszFail_literal_call c 31 installed
      simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
        hqr, hlim, nonzero, over, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, -evaluateHOLFiniteState_call]
      cases run : evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 31]) with
      | mk result post =>
        rw [run] at fail
        cases result with
        | none => exact absurd rfl fail.2.2.2.1
        | some x =>
          try simp only
          refine ⟨fail.1, fail.2.1, fail.2.2.1, by simp, ?_⟩
          intro v equal
          exact absurd equal (fail.2.2.2.2 v)
    · simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, hqr, hlim, nonzero, over, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite]
  · have fail := sszFail_literal_call c 30 installed
    have nonzero' : ¬ r = 0#64 := nonzero
    simp [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact,
      hqr, hlim, nonzero', Flapjack.Compiler.Encoders.Asm.wordCmpHOL, -evaluateHOLFiniteState_call]
    cases run : evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 30]) with
    | mk result post =>
      rw [run] at fail
      cases result with
      | none => exact absurd rfl fail.2.2.2.1
      | some x =>
        try simp only
        refine ⟨fail.1, fail.2.1, fail.2.2.1, by simp, ?_⟩
        intro v equal
        exact absurd equal (fail.2.2.2.2 v)

#print axioms sszFail_literal_call
#print axioms evaluate_sszFixedListCountTail
end InitECandidate.Runtime
