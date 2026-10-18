import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionNonceWordArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.var .local (ofString "k"),.const 8,.const 12]
def transactionNonceU256Arguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.var .local (ofString "k"),.const 32]
def transactionNonceWiden : ProgHOL 64 :=
  .assign .local (ofString "v") (.rstruct [.var .local (ofString "w"),.const 0,.const 0,.const 0])
def transactionNonceBranch : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "t")) (.const 4))
    (.seq (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") transactionNonceWordArguments) transactionNonceWiden)
    (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionNonceU256Arguments)
def transactionNonceStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const 16]) (.var .local (ofString "v"))
def transactionNonceField : ProgHOL 64 := .seq transactionNonceBranch transactionNonceStore

theorem source_transaction_nonce : transactionAt 19 = .seq transactionNonceBranch (.seq transactionNonceStore (transactionAt 21)) := by
  simp only [transactionNonceBranch,transactionNonceWordArguments,transactionNonceU256Arguments,transactionNonceWiden,transactionNonceStore,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_nonce_field_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notWord : key ≠ ofString "w") (notValue : key ≠ ofString "v")
    (run : evaluateHOLFiniteState state transactionNonceField = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionNonceField _ state post run
  simp [transactionNonceField,transactionNonceBranch,transactionNonceWiden,transactionNonceStore,normalLocalFrameSyntax,
    Ne.symm notWord,Ne.symm notValue]

#print axioms source_transaction_nonce
#print axioms transaction_nonce_field_other_local
end InitECandidate.Runtime
