import InitECandidate.Runtime.AuthorizationsCidSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationRecordScope := authorizationAt 9
def authorizationEntryCheck := authorizationAt 8

theorem source_authorization_record_scope : authorizationRecordScope =
    .dec (ofString "a") .one
      (.op .add [.var .local (ofString "recs"),.panop .mul [.var .local (ofString "i"),.const 120]])
      authorizationCidDeclaration := by
  simp only [authorizationRecordScope,authorizationCidDeclaration,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_entry_check : authorizationEntryCheck =
    .seq (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
      (.raise (ofString "TxErr") (.const 20)) .skip) authorizationRecordScope := by
  simp only [authorizationEntryCheck,authorizationRecordScope,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_record_scope
end InitECandidate.Runtime
