import InitECandidate.Runtime.ChargeGasFailureCall
import InitECandidate.Runtime.Jumpdest
import InitECandidate.Runtime.OriginalOpcodeCode
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- JUMPDEST with zero gas raises before incrementing PC. -/
theorem evaluate_jumpdest_outOfGas_body (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : BitVec 64) (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64))
    (leftMemory : state.memory (frame + 64) = .word 0) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_op_jumpdest) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))),
        emptyLocalsHOLFinite {state with clock := state.clock - 1}) := by
  rw [source_jumpdest_body]
  apply evaluate_seq_some
  exact evaluate_chargeGas_outOfGas_call state (.const 1) frame 0 1
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code clock frameGlobal
    exceptionShape leftDomain leftMemory (by decide)

/-- The real opcode call propagates the gas exception in two clocks. -/
theorem evaluate_jumpdest_outOfGas_call (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : BitVec 64) (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64))
    (leftMemory : state.memory (frame + 64) = .word 0) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "op_jumpdest") []) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))),
        emptyLocalsHOLFinite {state with clock := state.clock - 2}) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have body := evaluate_jumpdest_outOfGas_body entry frame code
    (by change state.clock - 1 ≠ 0; omega) frameGlobal exceptionShape leftDomain leftMemory
  have installed : state.code.lookup (ofString "op_jumpdest") =
      some ([],sourceFunctionBody Guest.guestFn_op_jumpdest,.one) := by
    rw [code]; exact originalRuntimeCode_opJumpdest_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "op_jumpdest")
    (sourceFunctionBody Guest.guestFn_op_jumpdest) installed
  have call := evaluateHOLFiniteState_call_exception_no_handler state none (ofString "op_jumpdest") [] []
    (sourceFunctionBody Guest.guestFn_op_jumpdest) HolFiniteMapExact.empty .one (ofString "EvmErr")
    (.val (.word 4)) (emptyLocalsHOLFinite {entry with clock := entry.clock - 1})
    (by simp [evalListHOLFinite,evalListHOLExact]) lookup (by omega) body
  simpa only [entry,callEntryStateHOLFinite,emptyLocalsHOLFinite,Nat.sub_sub] using call

#print axioms evaluate_jumpdest_outOfGas_body
#print axioms evaluate_jumpdest_outOfGas_call
end InitECandidate.Runtime
