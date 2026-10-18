import InitECandidate.Runtime.AccessListSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_decode_transaction_rlp
  | n+1 => authorizationNext (transactionAt n)
def transactionSignatureLast := transactionAt 43

def transactionSignatureLastArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.op .add [.var .local (ofString "k"),.const 2],.const 32]
def transactionSignatureLastTail : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "tx"),.const 352]) (.var .local (ofString "v")))
    (.return (.var .local (ofString "tx")))

theorem source_transaction_signature_last : transactionSignatureLast =
    .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionSignatureLastArguments)
      transactionSignatureLastTail := by
  simp only [transactionSignatureLast,transactionSignatureLastArguments,transactionSignatureLastTail,transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_transaction_signature_last
end InitECandidate.Runtime
