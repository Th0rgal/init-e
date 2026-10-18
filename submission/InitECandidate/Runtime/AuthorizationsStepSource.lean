import InitECandidate.Runtime.AuthorizationsItemCheckSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def authorizationStep := authorizationAt 5
def authorizationStepArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.rfield 0 (.var .local (ofString "lst")),.panop .mul [.var .local (ofString "i"),.const 16]]),
   .load .one (.op .add [.rfield 0 (.var .local (ofString "lst")),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])]

theorem source_authorization_step : authorizationStep =
    .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item") authorizationStepArguments authorizationItemCheck := by
  simp only [authorizationStep,authorizationStepArguments,authorizationItemCheck,authorizationAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_authorization_step
end InitECandidate.Runtime
