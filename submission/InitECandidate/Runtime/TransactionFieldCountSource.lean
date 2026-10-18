import InitECandidate.Runtime.TransactionDecoderSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionFieldCountGuard : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "lst"))) (.var .local (ofString "nfields")))
    (.raise (ofString "TxErr") (.const 4)) .skip

theorem source_transaction_field_count : transactionAt 14 =
    .seq transactionFieldCountGuard (transactionAt 15) := by
  simp only [transactionFieldCountGuard,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_transaction_field_count
end InitECandidate.Runtime
