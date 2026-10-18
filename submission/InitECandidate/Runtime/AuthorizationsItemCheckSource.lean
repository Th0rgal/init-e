import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationItemCheck := authorizationAt 6

theorem source_authorization_item_check : authorizationItemCheck =
    .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
      (.raise (ofString "TxErr") (.const 20)) .skip) authorizationInnerSlices := by
  simp only [authorizationItemCheck,authorizationInnerSlices,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_item_check
end InitECandidate.Runtime
