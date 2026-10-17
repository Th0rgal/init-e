import InitECandidate.Runtime.ScratchReleaseBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationCleanupHandler : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_validate_items with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq (.call (some (_,some (_,_,handler))) _ _) _)) => handler
  | _ => .skip

theorem source_rlpValidation_cleanup_handler : rlpValidationCleanupHandler =
    .seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")])
      (.raise (ofString "RlpErr") (.var .local (ofString "e"))) := by
  simp only [rlpValidationCleanupHandler,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual validator exception handler has a one-tick budget even if
release or rethrow fails; no scratch-global or exception-value premise is needed. -/
theorem evaluate_rlpValidation_cleanup_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64)
    (markLocal : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    let evaluated := evaluateHOLFiniteState state rlpValidationCleanupHandler
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut := by
  let release : ProgHOL 64 := ProgHOL.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")]
  let rethrow : ProgHOL 64 := ProgHOL.raise (ofString "RlpErr") (.var .local (ofString "e"))
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "mark")] = some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,markLocal]
  have bounded := evaluate_scratchRelease_call_bounded state (.var .local (ofString "mark")) mark args code ticks
  have safe := evaluate_sequence_no_timeout state release rethrow bounded.2
    (fun next => evaluate_straightLine_no_timeout rethrow (by rfl) next)
  rw [source_rlpValidation_cleanup_handler]
  change (evaluateHOLFiniteState state (.seq release rethrow)).2.clock = state.clock - 1 ∧
    (evaluateHOLFiniteState state (.seq release rethrow)).1 ≠ some .timeOut
  refine ⟨?_,safe⟩
  cases run : evaluateHOLFiniteState state release with
  | mk result post =>
    change (evaluateHOLFiniteState state release).2.clock = state.clock - 1 ∧ _ at bounded
    rw [run] at bounded
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none => exact (clockPreserving_raise (ofString "RlpErr") (.var .local (ofString "e")) post).trans bounded.1
    | some result => exact bounded.1

#print axioms evaluate_rlpValidation_cleanup_bounded
end InitECandidate.Runtime
