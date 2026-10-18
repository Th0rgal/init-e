import InitECandidate.Runtime.PayloadStoreTailBound
import InitECandidate.Runtime.StraightLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadTransactionHeader : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "pl"),.const 32])
      (.rfield 0 (.var .local (ofString "txs"))))
    (.store (.op .add [.var .local (ofString "pl"),.const 40])
      (.rfield 1 (.var .local (ofString "txs"))))

theorem source_payload_transaction_header : payloadAt 17 =
    .seq (.store (.op .add [.var .local (ofString "pl"),.const 32])
      (.rfield 0 (.var .local (ofString "txs"))))
    (.seq (.store (.op .add [.var .local (ofString "pl"),.const 40])
      (.rfield 1 (.var .local (ofString "txs")))) (payloadAt 19)) := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The transaction-array header stores preserve locals and allocator globals
and consume no source ticks, including failures. -/
theorem evaluate_payload_transaction_header_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let evaluated := evaluateHOLFiniteState state payloadTransactionHeader
    evaluated.2.clock = state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      (∀ key, evaluated.2.locals.lookup key = state.locals.lookup key) ∧
      (∀ key, evaluated.2.globals.lookup key = state.globals.lookup key) := by
  exact ⟨clockPreserving_of_straightLine _ (by rfl) state,
    evaluate_straightLine_no_timeout _ (by rfl) state,
    fun key => evaluate_straight_local_frame key _ (by rfl) state,
    fun key => evaluate_avoidsGlobalAssignment key _ (by rfl) state⟩

#print axioms source_payload_transaction_header
#print axioms evaluate_payload_transaction_header_frame
end InitECandidate.Runtime
