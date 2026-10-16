import InitECandidate.Runtime.OpcodeComparison
import InitECandidate.Proofs.FrontendCodecComputation
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The authoritative dispatcher selects JUMPDEST at opcode 91 and returns
immediately after the selected opcode call. -/
theorem evaluate_dispatch_jumpdest_path {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (opcode : state.locals.lookup (ofString "op") = some (.val (.word 91)))
    (step : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "op_jumpdest") []) = (none,post)) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_dispatch) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite post) := by
  classical
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp (config := {maxSteps := 1000000}) only [Guest.guestFn_op_dispatch,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  have returned (s : PanSemStateFiniteExact 64 F) (word : BitVec 64) :
      evaluateHOLFiniteState s (.return (.const word)) =
        (some (.returned (.val (.word word))),emptyLocalsHOLFinite s) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  simp (config := {maxSteps := 1000000}) [-evaluateHOLFiniteState_return,-evaluateHOLFiniteState_ite,
    evaluateHOLFiniteState_seq_line780,
    evaluate_opcode_ite state 91 opcode,
    Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,evaluateHOLFiniteState_skip,returned,step]

#print axioms evaluate_dispatch_jumpdest_path
end InitECandidate.Runtime
