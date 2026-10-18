import InitECandidate.Runtime.TransactionHandledCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionWrapperArguments : List (ExpHOL 64) :=
  [.var .local (ofString "p"),.var .local (ofString "len")]
def transactionWrapperHandler : ProgHOL 64 :=
  .raise (ofString "TxErr") (.op .add [.const 100,.var .local (ofString "rc")])
def transactionWrapperCall : ProgHOL 64 :=
  .call (some (some (.local,ofString "tx"),some (ofString "RlpErr",ofString "rc",transactionWrapperHandler)))
    (ofString "decode_transaction_rlp") transactionWrapperArguments

theorem source_transaction_wrapper : sourceFunctionBody Guest.guestFn_decode_transaction =
    .dec (ofString "tx") .one (.const 0)
      (.dec (ofString "rc") .one (.const 0)
        (.seq transactionWrapperCall (.return (.var .local (ofString "tx"))))) := by
  simp only [transactionWrapperCall,transactionWrapperHandler,transactionWrapperArguments,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_wrapper_handler_straight : straightLine transactionWrapperHandler = true := by rfl

#print axioms source_transaction_wrapper
#print axioms transaction_wrapper_handler_straight
end InitECandidate.Runtime
