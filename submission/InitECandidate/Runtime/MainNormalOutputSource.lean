import InitECandidate.Runtime.MainSszHandlerSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def mainNormalSerializeArguments : List (ExpHOL 64) :=
 [.var .local (ofString "out"),.var .local (ofString "root"),.var .local (ofString "succ"),
  .load .one (.op .add [.var .local (ofString "si"),.const 88]),.const 5377]
def mainNormalOutputArguments : List (ExpHOL 64) := mainSszOutputArguments
def mainNormalErrorStore : ProgHOL 64 :=
 .storeByte (.op .add [.var .local (ofString "out"),.var .local (ofString "n")])
  (.var .global (ofString "fail_code"))
def mainNormalHalt : ProgHOL 64 :=
 .seq (.extCall (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)) (.return (.const 0))
def mainNormalOutput : ProgHOL 64 :=
 .seq mainNormalErrorStore (.seq (.call (some (none,none)) (ofString "output_write") mainNormalOutputArguments) mainNormalHalt)
def mainNormalSerialization : ProgHOL 64 :=
 .decCall (ofString "n") .one (ofString "serialize_result") mainNormalSerializeArguments mainNormalOutput
/-- Exact original main suffix after VM verification returns. -/
theorem source_main_normal_serialization : mainAt 24=mainNormalSerialization := by
 simp only [mainAt,statelessNext,sourceFunctionBody,
  InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl
#print axioms source_main_normal_serialization
end InitECandidate.Runtime
