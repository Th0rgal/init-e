import InitECandidate.Runtime.RlpSlicesSource
import InitECandidate.Runtime.RlpUncheckedDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_updates_straight : straightLine rlpSlicesUpdates = true := by
  simp only [rlpSlicesUpdates,rlpSlicesStep,rlpSlicesLoop,rlpSlicesLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A complete original slice iteration costs at most eleven source ticks,
including failed reads, failed stores, and unchecked item-length rejection. -/
theorem evaluate_rlpSlices_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer offset : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpSlicesStep
    state.clock ≤ evaluated.2.clock + 11 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_rlpSlices_step]
  exact evaluate_rlpUnchecked_declaration_bounded state (ofString "total")
    [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] rlpSlicesUpdates
    rlpSlices_updates_straight (pointer + offset)
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,offsetLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]) code ticks

#print axioms evaluate_rlpSlices_step_bounded
end InitECandidate.Runtime
