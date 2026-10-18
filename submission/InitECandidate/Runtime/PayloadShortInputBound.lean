import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.SszFailCallBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadLengthGuard : ProgHOL 64 :=
  .ite (.cmp .lower (.var .local (ofString "len")) (.const 540))
    (.call (some (none,none)) (ofString "ssz_fail") [.const 50]) .skip

theorem source_payload_length_guard : sourceFunctionBody Guest.guestFn_decode_payload =
    .seq payloadLengthGuard (payloadAt 1) := by
  simp only [payloadLengthGuard,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Short payloads reject within the single SSZ failure-call entry tick,
without allocating or inspecting their input bytes. -/
theorem evaluate_payload_short_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (small : length < (540 : BitVec 64)) (code : state.code = originalRuntimeCode)
    (nonzero : state.clock ≠ 0) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "len")) (.const 540)) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
    exact small
  have bounded := evaluate_sszFail_call_bounded state (.const 50) 50 code nonzero (by rfl)
  rw [source_payload_length_guard,evaluateHOLFiniteState_seq_line780]
  unfold payloadLengthGuard
  rw [evaluateHOLFiniteState_ite,condition]
  dsimp only
  rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
  cases ran : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const 50]) with
  | mk result post =>
    rw [ran] at bounded
    dsimp only at bounded ⊢
    cases result with
    | none => exact False.elim (bounded.2.2 rfl)
    | some result =>
      dsimp only
      exact ⟨by have h := bounded.1; omega,by have h := bounded.1; omega,bounded.2.1,by simp⟩

#print axioms evaluate_payload_short_input_bounded
end InitECandidate.Runtime
