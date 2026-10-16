import InitECandidate.Runtime.JumpdestFailure
import InitECandidate.Runtime.DispatchJumpdestExceptionPath
import InitECandidate.Runtime.OriginalDispatchCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The dispatcher propagates JUMPDEST's gas failure without changing memory. -/
theorem evaluate_dispatch_jumpdest_outOfGas_body (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : BitVec 64) (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (opcode : state.locals.lookup (ofString "op") = some (.val (.word 91)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64)) (leftMemory : state.memory (frame + 64) = .word 0) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_dispatch) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))),
        emptyLocalsHOLFinite {state with clock := state.clock - 2}) := by
  exact evaluate_dispatch_jumpdest_exception_path state _ (ofString "EvmErr") (.val (.word 4)) opcode
    (evaluate_jumpdest_outOfGas_call state frame code clock frameGlobal exceptionShape leftDomain leftMemory)

/-- A dispatcher call without a handler exposes the exception at its caller
boundary after three clocks. The frame loop supplies a handler at this boundary. -/
theorem evaluate_dispatch_jumpdest_outOfGas_call (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word 91)])
    (code : state.code = originalRuntimeCode) (clock : 3 ≤ state.clock)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64)) (leftMemory : state.memory (frame + 64) = .word 0) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "op_dispatch") [argument]) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))),
        emptyLocalsHOLFinite {state with clock := state.clock - 3}) := by
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
  have call := evaluateHOLFiniteState_call_exception_no_handler state none (ofString "op_dispatch")
    [argument] [.val (.word 91)] (sourceFunctionBody Guest.guestFn_op_dispatch) callee .one
    (ofString "EvmErr") (.val (.word 4)) (emptyLocalsHOLFinite {entry with clock := entry.clock - 2})
    arguments lookup (by omega) body
  simpa only [entry,callEntryStateHOLFinite,emptyLocalsHOLFinite,Nat.sub_sub] using call

#print axioms evaluate_dispatch_jumpdest_outOfGas_body
#print axioms evaluate_dispatch_jumpdest_outOfGas_call
end InitECandidate.Runtime
