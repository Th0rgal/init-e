import InitECandidate.Runtime.RunFramesDispatchScope
import InitECandidate.Runtime.DispatchCallProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Local environment at the opcode call within a complete loop body. -/
def runFramesLoopDispatchEntry {F : Type} (state : PanSemStateFiniteExact 64 F) (pc : BitVec 64) :=
  runFramesDispatchEntry (setVarHOLFinite (ofString "done") (.val (.word 0)) state) pc

theorem evaluate_runFrames_loop_dispatch {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (continuation frame pc length active : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (dispatch : evaluateHOLFiniteState (runFramesLoopDispatchEntry state pc) runFramesDispatchCall = (none,post))
    (locals : post.locals = (runFramesLoopDispatchEntry state pc).locals) :
    evaluateHOLFiniteState state runFramesLoopBody = (none,{post with locals := state.locals}) := by
  let entered := setVarHOLFinite (ofString "done") (.val (.word 0)) state
  have selected := evaluate_runFrames_running_precheck entered continuation frame active
    contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
  have dispatched := evaluate_runFrames_running_dispatch entered post frame pc length frameGlobal
    pcDomain pcMemory lengthDomain lengthMemory inside dispatch locals
  exact evaluate_runFrames_running_loop_body state {post with locals := entered.locals}
    (selected.trans dispatched) rfl

/-- A real JUMPDEST iteration spends one gas unit and four source clocks.
The while guard's own clock decrement is accounted separately. -/
theorem runFrames_jumpdest_loop_progress
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame pc length active : BitVec 64) (funding : GasFunding)
    (code : state.code = originalRuntimeCode)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (memory : HasGasFunding state frame funding)
    (clock : 4 ≤ state.clock)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (enough : (1 : BitVec 64) ≤ funding.left) (budget : funding.potential ≤ 200000000)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 91)]) :
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody = (none,post) ∧
      HasGasFunding post frame (funding.charge 1) ∧ post.clock = state.clock - 4 ∧
      post.memory (frame + 0) = .word (pc + 1) ∧ post.locals = state.locals ∧
      (funding.charge 1).used.toNat = funding.used.toNat + 1 := by
  obtain ⟨post,dispatch,funded,ticks,pcValue,_,_,_,locals,_,growth⟩ :=
    original_dispatch_jumpdest_call_progress (runFramesLoopDispatchEntry state pc)
      runFramesOpcodeExpression (some runFramesExceptionHandler) arguments frame pc funding code clock
      frameGlobal pcDomain pcMemory leftDomain usedDomain memory enough budget
  have body := evaluate_runFrames_loop_dispatch state post continuation frame pc length active
    contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
    pcDomain pcMemory lengthDomain lengthMemory inside dispatch locals
  exact ⟨{post with locals := state.locals},body,funded,ticks,pcValue,rfl,growth⟩

/-- STOP costs no gas but clears the active flag, so the following iteration
    takes the finite frame-finalization path instead of dispatching again. -/
theorem runFrames_stop_loop_progress
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame pc length active : BitVec 64) (funding : GasFunding)
    (code : state.code = originalRuntimeCode)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (memory : HasGasFunding state frame funding)
    (clock : 3 ≤ state.clock)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 0)]) :
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody = (none,post) ∧
      post.memory (frame + 104) = .word 0 ∧ HasGasFunding post frame funding ∧
      post.clock = state.clock - 3 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.locals = state.locals := by
  obtain ⟨post,dispatch,inactive,funded,ticks,pcValue,_,_,_,locals⟩ :=
    original_dispatch_stop_call_progress (runFramesLoopDispatchEntry state pc)
      runFramesOpcodeExpression (some runFramesExceptionHandler) arguments frame pc funding code clock
      frameGlobal pcDomain pcMemory activeDomain memory
  have body := evaluate_runFrames_loop_dispatch state post continuation frame pc length active
    contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
    pcDomain pcMemory lengthDomain lengthMemory inside dispatch locals
  exact ⟨{post with locals := state.locals},body,inactive,funded,ticks,pcValue,rfl⟩

#print axioms runFrames_stop_loop_progress
#print axioms evaluate_runFrames_loop_dispatch
#print axioms runFrames_jumpdest_loop_progress
end InitECandidate.Runtime
