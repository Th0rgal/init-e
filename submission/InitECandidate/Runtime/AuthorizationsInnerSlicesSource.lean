import InitECandidate.Runtime.AuthorizationsRecordSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationInnerSlices := authorizationAt 7

theorem source_authorization_inner_slices : authorizationInnerSlices =
    .decCall (ofString "ent") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] authorizationEntryCheck := by
  simp only [authorizationInnerSlices,authorizationEntryCheck,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_inner_slices
end InitECandidate.Runtime
