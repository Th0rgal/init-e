import InitECandidate.Runtime.AccessListItemCheckBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessStepArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.rfield 0 (.var .local (ofString "lst")),.panop .mul [.var .local (ofString "i"),.const 16]]),
   .load .one (.op .add [.rfield 0 (.var .local (ofString "lst")),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])]

theorem source_access_step : accessStep =
    .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item") accessStepArguments accessItemCheck := by
  simp only [accessStep,accessStepArguments,accessItemCheck,accessAt,authorizationNext,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_access_step
end InitECandidate.Runtime
