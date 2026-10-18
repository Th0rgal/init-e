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

def transactionSignatureMiddle := transactionAt 41

def transactionSignatureMiddleArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.op .add [.var .local (ofString "k"),.const 1],.const 32]
def transactionSignatureMiddleStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const 320]) (.var .local (ofString "v"))
def transactionSignatureMiddleField : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionSignatureMiddleArguments)
    transactionSignatureMiddleStore

theorem source_transaction_signature_middle : transactionSignatureMiddle =
    .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionSignatureMiddleArguments)
      (.seq transactionSignatureMiddleStore transactionSignatureLast) := by
  simp only [transactionSignatureMiddle,transactionSignatureMiddleArguments,transactionSignatureMiddleStore,transactionSignatureLast,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def transactionSignatureFirst := transactionAt 39

def transactionSignatureFirstArguments : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),.var .local (ofString "k"),.const 32]
def transactionSignatureFirstStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const 288]) (.var .local (ofString "v"))
def transactionSignatureFirstField : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionSignatureFirstArguments)
    transactionSignatureFirstStore

theorem source_transaction_signature_first : transactionSignatureFirst =
    .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") transactionSignatureFirstArguments)
      (.seq transactionSignatureFirstStore transactionSignatureMiddle) := by
  simp only [transactionSignatureFirst,transactionSignatureFirstArguments,transactionSignatureFirstStore,transactionSignatureMiddle,
    transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def transactionAuthorizationBranch : ProgHOL 64 :=
  match transactionAt 38 with | .seq branch _ => branch | _ => .skip
def transactionAuthorizationDecode : ProgHOL 64 :=
  match transactionAuthorizationBranch with
  | .ite _ (.decCall _ _ _ _ tail) _ => tail
  | _ => .skip

def transactionAuthorizationFinish : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "tx"),.const 272]) (.rfield 0 (.var .local (ofString "au"))))
    (.seq (.store (.op .add [.var .local (ofString "tx"),.const 280]) (.rfield 1 (.var .local (ofString "au"))))
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1])))

theorem source_transaction_authorization_decode : transactionAuthorizationDecode =
    .decCall (ofString "au") (.comb [.one,.one]) (ofString "decode_authorizations")
      [.rfield 0 (.var .local (ofString "aul")),.rfield 1 (.var .local (ofString "aul"))] transactionAuthorizationFinish := by
  simp only [transactionAuthorizationDecode,transactionAuthorizationBranch,transactionAuthorizationFinish,transactionAt,
    authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def transactionAccessBranch : ProgHOL 64 :=
  match transactionAt 36 with | .seq branch _ => branch | _ => .skip
def transactionAccessDecode : ProgHOL 64 :=
  match transactionAccessBranch with
  | .ite _ (.decCall _ _ _ _ tail) _ => tail
  | _ => .skip

def transactionAccessFinish : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "tx"),.const 208]) (.rfield 0 (.var .local (ofString "acc"))))
    (.seq (.store (.op .add [.var .local (ofString "tx"),.const 216]) (.rfield 1 (.var .local (ofString "acc"))))
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1])))

theorem source_transaction_access_decode : transactionAccessDecode =
    .decCall (ofString "acc") (.comb [.one,.one]) (ofString "decode_access_list")
      [.rfield 0 (.var .local (ofString "al")),.rfield 1 (.var .local (ofString "al"))] transactionAccessFinish := by
  simp only [transactionAccessDecode,transactionAccessBranch,transactionAccessFinish,transactionAt,
    authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_transaction_signature_last
end InitECandidate.Runtime
