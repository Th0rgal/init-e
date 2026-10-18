import InitECandidate.Runtime.TransactionAccessLocalProgress
import InitECandidate.Runtime.TransactionBlobLocalProgress
import InitECandidate.Runtime.TransactionBlobLocalFrame
import InitECandidate.Runtime.TransactionAuthorizationLocalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionTypedFields : ProgHOL 64 :=
  .seq transactionAccessBranch (.seq transactionBlobBranch transactionAuthorizationBranch)

def transactionAfterTypedIndex (kind index : BitVec 64) : BitVec 64 :=
  let access := if kind = 0#64 then index else index + 1
  let blob := if kind = 3#64 then access + 2 else access
  if kind = 4#64 then blob + 1 else blob

/-- The three actual optional transaction branches compose without assuming any decoder succeeds. -/
theorem transaction_typed_fields_index {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (kind index : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state transactionTypedFields = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (transactionAfterTypedIndex kind index))) := by
  unfold transactionTypedFields at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases accessRun : evaluateHOLFiniteState state transactionAccessBranch with
  | mk result accessPost =>
    rw [accessRun] at run
    cases result with
    | some result => cases run
    | none =>
      have accessIndex := transaction_access_branch_index state accessPost kind index typeLocal indexLocal accessRun
      have accessType := (transaction_access_branch_other_local state accessPost (ofString "t") (by decide) accessRun).trans typeLocal
      dsimp only at run
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases blobRun : evaluateHOLFiniteState accessPost transactionBlobBranch with
      | mk result blobPost =>
        rw [blobRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          have blobIndex := transaction_blob_branch_index accessPost blobPost kind _ accessType accessIndex blobRun
          have blobType := (transaction_blob_branch_other_local accessPost blobPost (ofString "t") (by decide) (by decide) blobRun).trans accessType
          exact transaction_authorization_branch_index blobPost post kind _ blobType blobIndex run

/-- Caller locals used by the signature suffix survive all three optional branches. -/
theorem transaction_typed_fields_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notIndex : key ≠ ofString "k") (notValue : key ≠ ofString "v")
    (run : evaluateHOLFiniteState state transactionTypedFields = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  unfold transactionTypedFields at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases accessRun : evaluateHOLFiniteState state transactionAccessBranch with
  | mk result accessPost =>
    rw [accessRun] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases blobRun : evaluateHOLFiniteState accessPost transactionBlobBranch with
      | mk result blobPost =>
        rw [blobRun] at run
        cases result with
        | some result => cases run
        | none =>
          dsimp only at run
          exact (transaction_authorization_branch_other_local blobPost post key notIndex run).trans
            ((transaction_blob_branch_other_local accessPost blobPost key notIndex notValue blobRun).trans
              (transaction_access_branch_other_local state accessPost key notIndex accessRun))

#print axioms transaction_typed_fields_index
#print axioms transaction_typed_fields_other_local
end InitECandidate.Runtime
