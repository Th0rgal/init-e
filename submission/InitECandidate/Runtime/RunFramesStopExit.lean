import InitECandidate.Runtime.RunFramesRootTerminal
import InitECandidate.Runtime.RunFramesOpcodeLoad
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A root frame executing STOP exits the real frame loop in six clocks:
    four for STOP's iteration and two for the terminal iteration. -/
theorem runFrames_stop_root_exit
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame parent previous pc length active go : BitVec 64) (funding : GasFunding)
    (code : state.code = originalRuntimeCode) (clock : 6 ≤ state.clock)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go))) (goRunning : go ≠ 0)
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat) (memory : HasGasFunding state frame funding)
    (errorDomain : state.memaddrs (frame + 160))
    (errorMemory : state.memory (frame + 160) = .word 0)
    (kindDomain : state.memaddrs (continuation + 16))
    (kindMemory : state.memory (continuation + 16) = .word 0)
    (parentDomain : state.memaddrs (continuation + 0))
    (parentMemory : state.memory (continuation + 0) = .word parent)
    (previousDomain : state.memaddrs (continuation + 8))
    (previousMemory : state.memory (continuation + 8) = .word previous)
    (separate : ∀ offset : BitVec 64, offset ∈ [0,8,16,32] →
      continuation + offset ≠ frame + 0 ∧ continuation + offset ≠ frame + 104)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry (decClockHOLFinite state) pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [runFramesOpcodeExpression] =
        some [.val (.word 0)]) :
    ∃ post, evaluateHOLFiniteState state runFramesWhile = (none,post) ∧
      post.clock = state.clock - 6 ∧
      post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧
      post.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      post.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) := by
  obtain ⟨stopped,body,inactive,funded,ticks,pcValue,locals,postCode,globals,domain,footprint⟩ :=
    runFrames_stop_loop_progress (decClockHOLFinite state) continuation frame pc length active funding
      code contGlobal frameGlobal pendingDomain pendingMemory activeDomain activeMemory running
      pcDomain pcMemory lengthDomain lengthMemory inside memory
      (by change 3 ≤ state.clock - 1; omega) arguments
  have fieldPreserved (offset : BitVec 64) (member : offset ∈ [0,8,16,32]) :
      stopped.memory (continuation + offset) = state.memory (continuation + offset) :=
    footprint _ (separate offset member).1 (separate offset member).2
  have pendingAfter : stopped.memory (continuation + 32) = .word 0 := by
    rw [fieldPreserved 32 (by simp)]; exact pendingMemory
  have kindAfter : stopped.memory (continuation + 16) = .word 0 := by
    rw [fieldPreserved 16 (by simp)]; exact kindMemory
  have parentAfter : stopped.memory (continuation + 0) = .word parent := by
    rw [fieldPreserved 0 (by simp)]; exact parentMemory
  have previousAfter : stopped.memory (continuation + 8) = .word previous := by
    rw [fieldPreserved 8 (by simp)]; exact previousMemory
  have errorAfter : stopped.memory (frame + 160) = .word 0 := by
    rw [footprint (frame + 160) (by simp) (by simp)]; exact errorMemory
  have stoppedCode : stopped.code = originalRuntimeCode := postCode.trans code
  have stoppedCont := globals ▸ contGlobal
  have stoppedFrame := globals ▸ frameGlobal
  have stoppedGo := locals ▸ goLocal
  obtain ⟨post,terminal,finalTicks,_,goZero,parentGlobal,previousGlobal⟩ :=
    runFrames_root_terminal_while stopped continuation frame parent previous go stoppedCode
      (by change stopped.clock = state.clock - 1 - 3 at ticks; omega) goRunning
      stoppedCont stoppedFrame stoppedGo (domain ▸ pendingDomain) pendingAfter
      (domain ▸ activeDomain) inactive (domain ▸ errorDomain) errorAfter
      (domain ▸ kindDomain) kindAfter (domain ▸ parentDomain) parentAfter
      (domain ▸ previousDomain) previousAfter
  have step := evaluate_runFrames_while_step state stopped go goLocal goRunning (by omega) body (by omega)
  rw [terminal] at step
  refine ⟨post,step,?_,goZero,parentGlobal,previousGlobal⟩
  change stopped.clock = state.clock - 1 - 3 at ticks
  omega

/-- The same complete exit, with STOP read from actual source byte memory. -/
theorem runFrames_stop_byte_root_exit
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame parent previous pc length active go : BitVec 64) (funding : GasFunding)
    (code : state.code = originalRuntimeCode) (clock : 6 ≤ state.clock)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go))) (goRunning : go ≠ 0)
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (pcDomain : state.memaddrs (frame + 0)) (pcMemory : state.memory (frame + 0) = .word pc)
    (lengthDomain : state.memaddrs (frame + 56)) (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat) (memory : HasGasFunding state frame funding)
    (errorDomain : state.memaddrs (frame + 160))
    (errorMemory : state.memory (frame + 160) = .word 0)
    (kindDomain : state.memaddrs (continuation + 16))
    (kindMemory : state.memory (continuation + 16) = .word 0)
    (parentDomain : state.memaddrs (continuation + 0))
    (parentMemory : state.memory (continuation + 0) = .word parent)
    (previousDomain : state.memaddrs (continuation + 8))
    (previousMemory : state.memory (continuation + 8) = .word previous)
    (separate : ∀ offset : BitVec 64, offset ∈ [0,8,16,32] →
      continuation + offset ≠ frame + 0 ∧ continuation + offset ≠ frame + 104)
    (codePointer : BitVec 64)
    (codeDomain : state.memaddrs (frame + 48))
    (codeMemory : state.memory (frame + 48) = .word codePointer)
    (byte : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (codePointer + pc) = some 0) :
    ∃ post, evaluateHOLFiniteState state runFramesWhile = (none,post) ∧
      post.clock = state.clock - 6 ∧
      post.locals.lookup (ofString "go") = some (.val (.word 0)) ∧
      post.globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      post.globals.lookup (ofString "cur_cont") = some (.val (.word previous)) := by
  apply runFrames_stop_root_exit state continuation frame parent previous pc length active go funding
    code clock contGlobal frameGlobal goLocal goRunning pendingDomain pendingMemory activeDomain activeMemory
    running pcDomain pcMemory lengthDomain lengthMemory inside memory errorDomain errorMemory
    kindDomain kindMemory parentDomain parentMemory previousDomain previousMemory separate
  exact eval_runFrames_opcode_argument (decClockHOLFinite state) frame pc codePointer 0
    frameGlobal codeDomain codeMemory byte

#print axioms runFrames_stop_byte_root_exit
#print axioms runFrames_stop_root_exit
end InitECandidate.Runtime
