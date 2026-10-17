import InitECandidate.Runtime.RlpValidationHandledCallBound
import InitECandidate.Runtime.RlpValidationNormalCleanup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationWrapperCore : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_validate_items with
  | .decCall _ _ _ _ (.dec _ _ _ body) => body
  | _ => .skip

theorem source_rlpValidation_wrapper_core : rlpValidationWrapperCore =
    .seq (.call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
      (ofString "_rlp_validate_items_body") [.var .local (ofString "p"),.var .local (ofString "len")])
      rlpValidationNormalCleanup := by
  simp only [rlpValidationWrapperCore,rlpValidationCleanupHandler,rlpValidationNormalCleanup,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original wrapper core covers the handled validator call, normal
release and return, including every early failure and caught exception. -/
theorem evaluate_rlpValidation_wrapper_core_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (mark : BitVec 64)
    (markLocal : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationWrapperCore
    state.clock ≤ evaluated.2.clock + ((2 * length.toNat + 1) * 15 + 3) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  let called : ProgHOL 64 := .call (some (none,some (ofString "RlpErr",ofString "e",rlpValidationCleanupHandler)))
    (ofString "_rlp_validate_items_body") arguments
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  have bound := evaluate_rlpValidation_handled_call_bounded state arguments pointer length scratch frame ceiling inputLimit mark
    markLocal args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  change state.clock ≤ (evaluateHOLFiniteState state called).2.clock + ((2 * length.toNat + 1) * 15 + 2) ∧
    (evaluateHOLFiniteState state called).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState state called).1 ≠ some .timeOut at bound
  rw [source_rlpValidation_wrapper_core]
  change state.clock ≤ (evaluateHOLFiniteState state (.seq called rlpValidationNormalCleanup)).2.clock + _ ∧ _
  cases run : evaluateHOLFiniteState state called with
  | mk result post =>
    rw [run] at bound
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have locals := evaluate_rlpValidation_handled_normal_locals state post arguments run
      have metadata := evaluateHOLFiniteState_metadata state called
      rw [run] at metadata
      have tail := evaluate_rlpValidation_normal_cleanup_bounded post mark (by rw [locals]; exact markLocal)
        (metadata.1.trans code) (by dsimp only at bound; omega)
      dsimp only at bound tail ⊢
      exact ⟨by omega,by omega,tail.2.1,tail.2.2⟩
    | some result =>
      dsimp only at bound ⊢
      exact ⟨by omega,bound.2.1,bound.2.2,by simp⟩

#print axioms evaluate_rlpValidation_wrapper_core_bounded
end InitECandidate.Runtime
