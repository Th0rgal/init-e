import InitECandidate.Runtime.TransactionTypedSignatureBound
import InitECandidate.Runtime.TransactionPairHeaderPrefix
import InitECandidate.Runtime.NormalLocalIncrementCalls
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionDataArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.var .local (ofString "k")]
def transactionDataFinish : ProgHOL 64 := transactionPairFinish (ofString "data") 192 200 1
def transactionDataField : ProgHOL 64 :=
  .decCall (ofString "data") (.comb [.one,.one]) (ofString "tx_bytes_item") transactionDataArguments transactionDataFinish

/-- The actual data scope encloses the remaining original transaction suffix. -/
theorem source_transaction_data : transactionAt 32 =
    .decCall (ofString "data") (.comb [.one,.one]) (ofString "tx_bytes_item") transactionDataArguments
      (.seq (.store (.op .add [.var .local (ofString "tx"),.const 192]) (.rfield 0 (.var .local (ofString "data"))))
        (.seq (.store (.op .add [.var .local (ofString "tx"),.const 200]) (.rfield 1 (.var .local (ofString "data"))))
          (.seq (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1])) transactionTypedSignature))) := by
  rw [← source_transaction_typed_signature]
  simp only [transactionDataArguments,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The data field's own normal execution advances the index exactly once. -/
theorem transactionDataField_increments : NormalLocalIncrement (ofString "k") transactionDataField := by
  unfold transactionDataField transactionDataFinish transactionPairFinish
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  exact normalLocalIncrement_assign _

theorem transaction_data_field_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionDataField = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionDataField _ state post run
  simp [transactionDataField,transactionDataFinish,transactionPairFinish,normalLocalFrameSyntax,Ne.symm different]

#print axioms source_transaction_data
#print axioms transactionDataField_increments
#print axioms transaction_data_field_other_local
end InitECandidate.Runtime
