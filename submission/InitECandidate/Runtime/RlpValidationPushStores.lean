import InitECandidate.Runtime.RlpValidationPushUpdates
import InitECandidate.Runtime.DecodeStepExtensionStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpValidation_push_stores : rlpValidationPushStores =
    .seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
      (.seq (.store (.op .add [.var .local (ofString "rec"),.const 8]) (.var .local (ofString "end")))
        (.seq (.store (.op .add [.var .local (ofString "rec"),.const 16]) (.var .local (ofString "top")))
          rlpValidationPushUpdates)) := by
  simp only [rlpValidationPushStores,rlpValidationPushUpdates,rlpValidationListPush,rlpValidationAfterHeader,
    rlpValidationHeaderContinuation,rlpValidationHeaderCall,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Exact original stack-record writes, followed by the original payload
entry assignments. The stores do not alter locals or source clock. -/
theorem evaluate_rlpValidation_push_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top : BitVec 64)
    (recordLocal : state.locals.lookup (ofString "rec") = some (.val (.word record)))
    (afterLocal : state.locals.lookup (ofString "after") = some (.val (.word after)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (domain0 : state.memaddrs record) (domain8 : state.memaddrs (record + 8))
    (domain16 : state.memaddrs (record + 16)) :
    evaluateHOLFiniteState state rlpValidationPushStores =
      evaluateHOLFiniteState (sourceWriteWord (sourceWriteWord (sourceWriteWord state record after)
        (record + 8) stop) (record + 16) top) rlpValidationPushUpdates := by
  let first := sourceWriteWord state record after
  let second := sourceWriteWord first (record + 8) stop
  let third := sourceWriteWord second (record + 16) top
  have one : evaluateHOLFiniteState state
      (.store (.var .local (ofString "rec")) (.var .local (ofString "after"))) = (none,first) := by
    apply evaluate_store_word state record after
    · simpa [evalHOLExact] using recordLocal
    · simpa [evalHOLExact] using afterLocal
    · exact domain0
  have two : evaluateHOLFiniteState first
      (.store (.op .add [.var .local (ofString "rec"),.const 8]) (.var .local (ofString "end"))) = (none,second) := by
    apply evaluate_store_word first (record + 8) stop
    · simp [evalHOLExact,evalListHOLExact,first,sourceWriteWord,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · simpa [evalHOLExact,first,sourceWriteWord] using stopLocal
    · exact domain8
  have three : evaluateHOLFiniteState second
      (.store (.op .add [.var .local (ofString "rec"),.const 16]) (.var .local (ofString "top"))) = (none,third) := by
    apply evaluate_store_word second (record + 16) top
    · simp [evalHOLExact,evalListHOLExact,second,first,sourceWriteWord,recordLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · simpa [evalHOLExact,second,first,sourceWriteWord] using topLocal
    · exact domain16
  rw [source_rlpValidation_push_stores,evaluateHOLFiniteState_seq_line780,one]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,three]

#print axioms evaluate_rlpValidation_push_stores
end InitECandidate.Runtime
