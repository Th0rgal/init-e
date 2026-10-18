import InitECandidate.Proofs.FrontendCodecComputation
import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Follow the actual sequential continuation or loop body in the decoder. -/
def authorizationNext : ProgHOL 64 → ProgHOL 64
  | .seq (.while condition body) _ => .while condition body
  | .decCall _ _ _ _ body | .dec _ _ _ body | .seq _ body | .while _ body => body
  | _ => .skip

def authorizationAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_decode_authorizations
  | n + 1 => authorizationNext (authorizationAt n)

def authorizationLastScalar := authorizationAt 20
def authorizationLastStore := authorizationAt 21

theorem source_authorization_last_scalar : authorizationLastScalar =
    .decCall (ofString "s") (.comb [.one,.one,.one,.one]) (ofString "tx_scalar_u256")
      [.rfield 0 (.var .local (ofString "ent")),.const 5,.const 32] authorizationLastStore := by
  simp only [authorizationLastScalar,authorizationLastStore,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_authorization_last_store : authorizationLastStore =
    .seq (.store (.op .add [.var .local (ofString "a"),.const 88]) (.var .local (ofString "s")))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  simp only [authorizationLastStore,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem authorizationLastStore_straight : straightLine authorizationLastStore = true := by
  rw [source_authorization_last_store]
  rfl

#print axioms source_authorization_last_scalar
end InitECandidate.Runtime
