import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionToBranch : ProgHOL 64 :=
  .ite (.cmp .notLower (.var .local (ofString "t")) (.const 3))
    (.call (some (some (.local,ofString "w"),none)) (ofString "tx_fixed_bytes")
      [.var .local (ofString "arr"),.var .local (ofString "k"),.const 20])
    (.call (some (some (.local,ofString "w"),none)) (ofString "tx_to_item")
      [.var .local (ofString "arr"),.var .local (ofString "k")])
def transactionToStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const 152]) (.var .local (ofString "w"))
def transactionToField : ProgHOL 64 := .seq transactionToBranch transactionToStore

theorem source_transaction_to : transactionAt 26 = .seq transactionToBranch (.seq transactionToStore (transactionAt 28)) := by
  simp only [transactionToBranch,transactionToStore,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_to_field_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "w")
    (run : evaluateHOLFiniteState state transactionToField = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionToField _ state post run
  simp [transactionToField,transactionToBranch,transactionToStore,normalLocalFrameSyntax,Ne.symm different]

#print axioms source_transaction_to
#print axioms transaction_to_field_other_local
end InitECandidate.Runtime
