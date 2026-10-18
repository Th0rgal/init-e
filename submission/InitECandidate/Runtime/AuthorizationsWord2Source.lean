import InitECandidate.Runtime.AuthorizationsWordTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationWord2Declaration := authorizationAt 14
def authorizationWord2Store := authorizationAt 15

theorem source_authorization_word2_declaration : authorizationWord2Declaration =
    .decCall (ofString "w") .one (ofString "tx_scalar_word")
      [.rfield 0 (.var .local (ofString "ent")),.const 2,.const 8,.const 12] authorizationWord2Store := by
  simp only [authorizationWord2Declaration,authorizationWord2Store,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_word2_store : authorizationWord2Store =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 40]) (.var .local (ofString "w")))
      authorizationWordAssignAndTail := by
  simp only [authorizationWord2Store,authorizationWordAssignAndTail,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_word2_declaration
end InitECandidate.Runtime
