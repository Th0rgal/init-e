import InitECandidate.Runtime.AuthorizationsAddressSource
import InitECandidate.Runtime.AuthorizationsTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationCidDeclaration := authorizationAt 10
def authorizationCidStore := authorizationAt 11

theorem source_authorization_cid_declaration : authorizationCidDeclaration =
    .decCall (ofString "cid") (.comb [.one,.one,.one,.one]) (ofString "tx_scalar_u256")
      [.rfield 0 (.var .local (ofString "ent")),.const 0,.const 32] authorizationCidStore := by
  simp only [authorizationCidDeclaration,authorizationCidStore,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_cid_store : authorizationCidStore =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 0]) (.var .local (ofString "cid")))
      authorizationAddressDeclaration := by
  simp only [authorizationCidStore,authorizationAddressDeclaration,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_cid_declaration
end InitECandidate.Runtime
