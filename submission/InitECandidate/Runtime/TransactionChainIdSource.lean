import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionChainIdArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.const 0,.const 8,.const 12]
def transactionChainIdFinish : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "tx"),.const 8]) (.var .local (ofString "w")))
    (.assign .local (ofString "k") (.const 1))
def transactionChainIdBranch : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0))
    (.seq (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionChainIdArguments)
      transactionChainIdFinish) .skip

theorem source_transaction_chain_id : transactionAt 17 =
    .seq transactionChainIdBranch (transactionAt 18) := by
  simp only [transactionChainIdBranch,transactionChainIdArguments,transactionChainIdFinish,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_chain_id_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notWord : key ≠ ofString "w") (notIndex : key ≠ ofString "k")
    (run : evaluateHOLFiniteState state transactionChainIdBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionChainIdBranch _ state post run
  simp [transactionChainIdBranch,transactionChainIdFinish,normalLocalFrameSyntax,Ne.symm notWord,Ne.symm notIndex]

#print axioms source_transaction_chain_id
#print axioms transaction_chain_id_other_local
end InitECandidate.Runtime
