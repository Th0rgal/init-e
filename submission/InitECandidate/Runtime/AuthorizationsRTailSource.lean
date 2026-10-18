import InitECandidate.Runtime.AuthorizationsTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationRScalar := authorizationAt 18
def authorizationRStoreAndLast := authorizationAt 19

theorem source_authorization_r_scalar : authorizationRScalar =
    .decCall (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "tx_scalar_u256")
      [.rfield 0 (.var .local (ofString "ent")),.const 4,.const 32] authorizationRStoreAndLast := by
  simp only [authorizationRScalar,authorizationRStoreAndLast,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_r_store_and_last : authorizationRStoreAndLast =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 56]) (.var .local (ofString "r")))
      authorizationLastScalar := by
  simp only [authorizationRStoreAndLast,authorizationLastScalar,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_r_scalar
end InitECandidate.Runtime
