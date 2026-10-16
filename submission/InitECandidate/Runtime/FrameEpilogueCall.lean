import InitECandidate.Runtime.FrameEpilogue
import InitECandidate.Runtime.OriginalFrameEpilogueCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual successful epilogue call costs exactly its one call-entry clock;
    memory, globals and caller locals are unchanged. -/
theorem evaluate_frameEpilogue_success_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64) (code : state.code = originalRuntimeCode)
    (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (domain : state.memaddrs (frame + 160))
    (memory : state.memory (frame + 160) = .word 0) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "frame_epilogue") []) =
      (none,{state with clock := state.clock - 1}) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body := evaluate_frameEpilogue_success entry frame frameGlobal domain memory
  have installed : state.code.lookup (ofString "frame_epilogue") =
      some ([],sourceFunctionBody Guest.guestFn_frame_epilogue,.one) := by
    rw [code]; exact originalRuntimeCode_frameEpilogue_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "frame_epilogue")
    (sourceFunctionBody Guest.guestFn_frame_epilogue) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "frame_epilogue") [] []
    (sourceFunctionBody Guest.guestFn_frame_epilogue) HolFiniteMapExact.empty .one (.val (.word 0))
    (emptyLocalsHOLFinite entry) (by simp [evalListHOLFinite,evalListHOLExact]) lookup clock body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

#print axioms evaluate_frameEpilogue_success_call
end InitECandidate.Runtime
