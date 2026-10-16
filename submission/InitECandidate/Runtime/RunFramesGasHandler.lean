import InitECandidate.Runtime.DispatchGasFailure
import InitECandidate.Runtime.RunFramesSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real run_frames handler catches the gas exception after three clocks,
restores caller locals, binds err=4, and invokes frame_exception. -/
theorem evaluate_runFrames_outOfGas_handler (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame oldError : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 91)])
    (code : state.code = originalRuntimeCode) (clock : 3 ≤ state.clock)
    (errorLocal : state.locals.lookup (ofString "err") = some (.val (.word oldError)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64)) (leftMemory : state.memory (frame + 64) = .word 0) :
    evaluateHOLFiniteState state runFramesDispatchCall =
      evaluateHOLFiniteState
        (setVarHOLFinite (ofString "err") (.val (.word 4)) {state with clock := state.clock - 3})
        (.call (some (none,none)) (ofString "frame_exception") [.var .local (ofString "err")]) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "op",.val (.word 91))
  let entry := callEntryStateHOLFinite state callee
  have opcode : entry.locals.lookup (ofString "op") = some (.val (.word 91)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_dispatch_jumpdest_outOfGas_body entry frame code
    (by change 2 ≤ state.clock - 1; omega) opcode frameGlobal exceptionShape leftDomain leftMemory
  have installed : state.code.lookup (ofString "op_dispatch") =
      some ([(ofString "op",.one)],sourceFunctionBody Guest.guestFn_op_dispatch,.one) := by
    rw [code]; exact originalRuntimeCode_dispatch_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "op_dispatch") (ofString "op")
    (sourceFunctionBody Guest.guestFn_op_dispatch) 91 installed
  have call := evaluateHOLFiniteState_call_matched_exception_handler state none
    (ofString "EvmErr") (ofString "err") (ofString "op_dispatch")
    (.call (some (none,none)) (ofString "frame_exception") [.var .local (ofString "err")])
    (sourceFunctionBody Guest.guestFn_op_dispatch) [runFramesOpcodeExpression] [.val (.word 91)]
    callee .one (.val (.word 4)) (emptyLocalsHOLFinite {entry with clock := entry.clock - 2}) .one
    arguments lookup (by omega) body exceptionShape (by simp [shapeOfHOLExact,shapeEqHOL])
    (by simp [isValidValueHOLExact,lookupKvarHOLExact,errorLocal,shapeOfHOLExact,shapeEqHOL])
  simpa only [runFramesDispatchCall,runFramesExceptionHandler,entry,callEntryStateHOLFinite,
    emptyLocalsHOLFinite,Nat.sub_sub] using call

#print axioms evaluate_runFrames_outOfGas_handler
end InitECandidate.Runtime
