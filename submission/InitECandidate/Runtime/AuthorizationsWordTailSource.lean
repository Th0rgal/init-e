import InitECandidate.Runtime.AuthorizationsRTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationWordStoreAndRS := authorizationAt 17
def authorizationWordAssignAndTail := authorizationAt 16

theorem source_authorization_word_store_and_rs : authorizationWordStoreAndRS =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 48]) (.var .local (ofString "w")))
      authorizationRScalar := by
  simp only [authorizationWordStoreAndRS,authorizationRScalar,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_word_assignment : authorizationWordAssignAndTail =
    .seq (.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word")
      [.rfield 0 (.var .local (ofString "ent")),.const 3,.const 1,.const 12]) authorizationWordStoreAndRS := by
  simp only [authorizationWordAssignAndTail,authorizationWordStoreAndRS,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_word_assignment
end InitECandidate.Runtime
