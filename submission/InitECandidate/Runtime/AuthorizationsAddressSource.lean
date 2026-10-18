import InitECandidate.Runtime.AuthorizationsWord2Source
import InitECandidate.Runtime.AuthorizationsWordTailSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationAddressDeclaration := authorizationAt 12
def authorizationAddressStore := authorizationAt 13

theorem source_authorization_address_declaration : authorizationAddressDeclaration =
    .decCall (ofString "addr") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "ent")),.const 1,.const 20] authorizationAddressStore := by
  simp only [authorizationAddressDeclaration,authorizationAddressStore,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_address_store : authorizationAddressStore =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 32]) (.var .local (ofString "addr")))
      authorizationWord2Declaration := by
  simp only [authorizationAddressStore,authorizationWord2Declaration,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_address_declaration
end InitECandidate.Runtime
