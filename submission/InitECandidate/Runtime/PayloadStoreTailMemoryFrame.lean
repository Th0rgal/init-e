import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.PayloadOffsetReadWords
import InitECandidate.Runtime.BoundWordStoreChainFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Every remaining payload store is separated from a watched word.
The statement covers failed stores and unreadable input fields as well. -/
theorem evaluate_payload_store_tail_memory_frame {F : Type}
    (state : PanSemStateFiniteExact 64 F) (payload withdrawals watched : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atWithdrawals : state.locals.lookup (ofString "nwd") = some (.val (.word withdrawals)))
    (separate : ∀ offset : BitVec 64, offset ∈ ([48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
      watched ≠ payload + offset) :
    (evaluateHOLFiniteState state (payloadAt 20)).2.memory watched = state.memory watched := by
  apply evaluate_boundWordStoreChain_frame (bindings := state.locals) ?_ state rfl
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  change BoundWordStoreChainFrame state.locals watched (.seq (.store _ _) _)
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 48, ?_, separate 48 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 56, ?_, separate 56 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    refine ⟨withdrawals, ?_⟩
    simpa [evalHOLExact,locals,atWithdrawals,InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural] using evaluated.symm
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 64, ?_, separate 64 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 72, ?_, separate 72 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 80, ?_, separate 80 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 88, ?_, separate 88 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 96, ?_, separate 96 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 104, ?_, separate 104 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 112, ?_, separate 112 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 120, ?_, separate 120 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  apply BoundWordStoreChainFrame.store
  · intro current locals
    refine ⟨payload + 128, ?_, separate 128 (by simp)⟩
    simp [evalHOLExact,evalListHOLExact,locals,atPayload,wordOpHOL,wordOp,valueIsWord,valueWord,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural]
  · intro current locals parsed evaluated
    exact evaluated_binop_word current _ _ parsed evaluated
  exact BoundWordStoreChainFrame.tail _ rfl

/-- The transaction pointer and count survive the final payload stores. -/
theorem evaluate_payload_store_tail_transaction_cells {F : Type}
    (state : PanSemStateFiniteExact 64 F) (payload withdrawals : BitVec 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atWithdrawals : state.locals.lookup (ofString "nwd") = some (.val (.word withdrawals))) :
    (evaluateHOLFiniteState state (payloadAt 20)).2.memory (payload + 32) = state.memory (payload + 32) ∧
    (evaluateHOLFiniteState state (payloadAt 20)).2.memory (payload + 40) = state.memory (payload + 40) := by
  constructor
  all_goals
    apply evaluate_payload_store_tail_memory_frame state payload withdrawals _ atPayload atWithdrawals
    intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp

#print axioms evaluate_payload_store_tail_memory_frame
#print axioms evaluate_payload_store_tail_transaction_cells
end InitECandidate.Runtime
