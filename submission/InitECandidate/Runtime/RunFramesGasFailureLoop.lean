import InitECandidate.Runtime.RunFramesGasHandlerCall
import InitECandidate.Runtime.RunFramesErrorScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete gas-failure loop body: the exception is handled, pending is set,
and all three temporary source locals are restored, in six clocks. -/
theorem evaluate_runFrames_gas_failure_loop (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame continuation msg gas used spilled empty pc length active : BitVec 64)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 91)])
    (code : state.code = originalRuntimeCode) (clock : 6 ≤ state.clock)
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (emptyGlobal : state.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
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
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody =
        (none,post) ∧
      post.memory (continuation + 32) = .word 1 ∧ post.clock = state.clock - 6 ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals := by
  let entry := runFramesLoopDispatchEntry state pc
  have errorLocal : entry.locals.lookup (ofString "err") = some (.val (.word 0)) := by
    simp [entry,runFramesLoopDispatchEntry,runFramesDispatchEntry,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,dispatch,pending,ticks,globals,postCode,domain,locals⟩ :=
    evaluate_runFrames_gas_handler_call entry frame continuation msg gas used spilled empty 0
      arguments code clock errorLocal exceptionShape frameGlobal contGlobal emptyGlobal
      leftDomain usedDomain spillDomain stateDomain pointerDomain errorDomain dataDomain sizeDomain
      pendingDomain msgDomain leftMemory usedMemory spillMemory pointerMemory msgMemory separate
  have restoredLocals : post.locals = (setVarHOLFinite (ofString "err") (.val (.word 4))
      (setVarHOLFinite (ofString "pc") (.val (.word pc))
        (setVarHOLFinite (ofString "done") (.val (.word 0)) state))).locals := by
    rw [locals]
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : ofString "err" = key <;> simp [same,entry,runFramesLoopDispatchEntry,runFramesDispatchEntry,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_runFrames_loop_changed_err_dispatch state post continuation frame pc length active 4
    contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
    pcDomain pcMemory lengthDomain lengthMemory inside dispatch restoredLocals
  exact ⟨{post with locals := state.locals},body,pending,ticks,globals,postCode,domain,rfl⟩

#print axioms evaluate_runFrames_gas_failure_loop
end InitECandidate.Runtime
