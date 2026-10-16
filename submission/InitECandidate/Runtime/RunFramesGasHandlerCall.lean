import InitECandidate.Runtime.FrameExceptionCall
import InitECandidate.Runtime.RunFramesGasHandler
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete handled JUMPDEST gas failure at the actual run_frames call site:
three clocks to raise, three to handle, and a pending continuation afterward. -/
theorem evaluate_runFrames_gas_handler_call (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame continuation msg gas used spilled empty oldError : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 91)])
    (code : state.code = originalRuntimeCode) (clock : 6 ≤ state.clock)
    (errorLocal : state.locals.lookup (ofString "err") = some (.val (.word oldError)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (emptyGlobal : state.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (spillDomain : state.memaddrs (frame + 192)) (stateDomain : state.memaddrs (frame + 72))
    (pointerDomain : state.memaddrs (frame + 112)) (errorDomain : state.memaddrs (frame + 160))
    (dataDomain : state.memaddrs (frame + 120)) (sizeDomain : state.memaddrs (frame + 128))
    (pendingDomain : state.memaddrs (continuation + 32)) (msgDomain : state.memaddrs (msg + 48))
    (leftMemory : state.memory (frame + 64) = .word 0)
    (usedMemory : state.memory (frame + 184) = .word used)
    (spillMemory : state.memory (frame + 192) = .word spilled)
    (pointerMemory : state.memory (frame + 112) = .word msg)
    (msgMemory : state.memory (msg + 48) = .word gas) (separate : msg + 48 ≠ frame + 64) :
    ∃ post, evaluateHOLFiniteState state runFramesDispatchCall =
        (none,post) ∧
      post.memory (continuation + 32) = .word 1 ∧ post.clock = state.clock - 6 ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.locals = (setVarHOLFinite (ofString "err") (.val (.word 4)) state).locals := by
  let entered := setVarHOLFinite (ofString "err") (.val (.word 4)) {state with clock := state.clock - 3}
  have dispatch := evaluate_runFrames_outOfGas_handler state frame oldError arguments code (by omega)
    errorLocal frameGlobal exceptionShape leftDomain leftMemory
  have enteredError : entered.locals.lookup (ofString "err") = some (.val (.word 4)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,handler,pending,ticks,globals,postCode,domain,locals⟩ :=
    evaluate_frameException_error_call entered (.var .local (ofString "err"))
      frame continuation msg gas 0 used spilled 4 empty
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,enteredError]) code
      (by change 3 ≤ state.clock - 3; omega) frameGlobal contGlobal emptyGlobal (by decide)
      leftDomain usedDomain spillDomain stateDomain pointerDomain errorDomain dataDomain sizeDomain
      pendingDomain msgDomain leftMemory usedMemory spillMemory pointerMemory msgMemory separate
  have run : evaluateHOLFiniteState state runFramesDispatchCall = (none,post) := dispatch.trans handler
  refine ⟨post,run,pending,?_,globals,postCode,domain,locals⟩
  change post.clock = state.clock - 3 - 3 at ticks
  omega

#print axioms evaluate_runFrames_gas_handler_call
end InitECandidate.Runtime
