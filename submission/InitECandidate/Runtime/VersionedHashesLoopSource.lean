import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.TransactionSliceArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def versionedHashesAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes
  | n+1 => authorizationNext (versionedHashesAt n)
def versionedHashesLoop : ProgHOL 64 :=
  match versionedHashesAt 7 with | .seq loop _ => loop | _ => .skip
def versionedHashesStep : ProgHOL 64 :=
  match versionedHashesLoop with | .while _ body => body | _ => .skip
def versionedHashesScan : ProgHOL 64 :=
  match versionedHashesStep with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.seq scan _)) => scan
  | _ => .skip

theorem source_versioned_hashes_step : versionedHashesStep =
    .decCall (ofString "tx") .one (ofString "decode_transaction") (transactionSliceArguments (ofString "txs") (ofString "i"))
      (.decCall (ofString "isb") .one (ofString "tx_is_blob") [.var .local (ofString "tx")]
        (.seq versionedHashesScan (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := by
  simp only [versionedHashesScan,versionedHashesStep,versionedHashesLoop,versionedHashesAt,authorizationNext,
    transactionSliceArguments,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def versionedHashesBlobLoop : ProgHOL 64 :=
  match versionedHashesScan with | .ite _ (.dec _ _ _ (.dec _ _ _ loop)) _ => loop | _ => .skip
def versionedHashesBlobCondition : ExpHOL 64 :=
  match versionedHashesBlobLoop with | .while condition _ => condition | _ => .const 0
def versionedHashesBlobStep : ProgHOL 64 :=
  match versionedHashesBlobLoop with | .while _ body => body | _ => .skip

theorem source_versioned_hashes_scan : versionedHashesScan =
    .ite (.cmp .notEqual (.var .local (ofString "isb")) (.const 0))
      (.dec (ofString "nb") .one (.load .one (.op .add [.var .local (ofString "tx"),.const 264]))
        (.dec (ofString "j") .one (.const 0) versionedHashesBlobLoop)) .skip := by
  simp only [versionedHashesBlobLoop,versionedHashesScan,versionedHashesStep,versionedHashesLoop,versionedHashesAt,
    authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_versioned_hashes_blob_loop : versionedHashesBlobLoop =
    .while versionedHashesBlobCondition versionedHashesBlobStep := by
  simp only [versionedHashesBlobCondition,versionedHashesBlobStep,versionedHashesBlobLoop,versionedHashesScan,
    versionedHashesStep,versionedHashesLoop,versionedHashesAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_versioned_hashes_scan
#print axioms source_versioned_hashes_blob_loop
#print axioms source_versioned_hashes_step
end InitECandidate.Runtime
