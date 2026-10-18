import InitECandidate.Runtime.SszFailFreeFrame
import InitECandidate.Runtime.SszCheckOffsetsBody
import InitECandidate.Runtime.SszFixedListCountBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszCheckOffsets_failFree : sszFailFree (sourceFunctionBody Guest.guestFn_ssz_check_offsets) = true := by
  rw [source_sszCheckOffsets_body]; decide_cbv

/-- ssz_check_offsets preserves memory and globals on every continuing outcome, at any clock. -/
theorem evaluate_sszCheckOffsets_body_frame {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (installed : e.code = originalRuntimeCode)
    (benign : SszBenign (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)).1) :
    (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)).2.memory = e.memory ∧
      (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)).2.globals = e.globals :=
  evaluate_sszFailFree_frame _ sszCheckOffsets_failFree e installed benign

theorem sszFixedListCountTail_failFree : sszFailFree sszFixedListCountTail = true := by
  unfold sszFixedListCountTail; decide_cbv

def udivmodNonzeroBody : ProgHOL 64 :=
  .seq (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
      (.return (.rstruct [.const 0, .var .local (ofString "a")])) .skip) udivmodTail

theorem udivmodNonzeroBody_readOnly : readOnlyMemory udivmodNonzeroBody = true := by
  unfold udivmodNonzeroBody udivmodTail udivmodLoop udivmodStep; rfl

/-- With a nonzero divisor the trap branch is skipped. -/
theorem evaluate_udivmod_body_nonzero {σ : Type} (t : PanSemStateFiniteExact 64 σ) (b : BitVec 64)
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) :
    evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_udivmod) =
      evaluateHOLFiniteState t udivmodNonzeroBody := by
  rw [source_udivmod_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have cond : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .equal (.var .local (ofString "b")) (.const 0)) = some (.val (.word 0#64)) := by
    simp [evalHOLExact, hb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact nz
  rw [cond]
  dsimp only
  rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
  rfl

/-- Nonzero-divisor udivmod preserves memory and globals at every outcome. -/
theorem evaluate_udivmod_body_frame {σ : Type} (t : PanSemStateFiniteExact 64 σ) (b : BitVec 64)
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) :
    (evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_udivmod)).2.memory = t.memory ∧
      (evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_udivmod)).2.globals = t.globals := by
  rw [evaluate_udivmod_body_nonzero t b hb nz]
  exact ⟨evaluate_readOnly_memory _ udivmodNonzeroBody_readOnly t,
    evaluate_readOnly_globals _ udivmodNonzeroBody_readOnly t⟩

#print axioms evaluate_sszCheckOffsets_body_frame
#print axioms evaluate_udivmod_body_frame
end InitECandidate.Runtime
