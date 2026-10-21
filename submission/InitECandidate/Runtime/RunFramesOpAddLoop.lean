import InitECandidate.Runtime.RunFramesOpAddCall
import InitECandidate.Runtime.RunFramesIteration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Runtime.FineCost

set_option maxHeartbeats 4000000

/-- One real `run_frames` iteration whose current byte is ADD: the loop body
evaluates to `none`, charges exactly three gas units, advances the frame pc,
and decreases the clock by eight. -/
theorem runFrames_add_loop_progress (coeff : FineCost.Work)
    (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation frame sp cap base pc length active : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (pendingDomain : state.memaddrs (continuation + 32))
    (pendingMemory : state.memory (continuation + 32) = .word 0)
    (activeDomain : state.memaddrs (frame + 104))
    (activeMemory : state.memory (frame + 104) = .word active) (running : active ≠ 0)
    (lengthDomain : state.memaddrs (frame + 56))
    (lengthMemory : state.memory (frame + 56) = .word length)
    (inside : pc.toNat < length.toNat)
    (inv : GuestFrameInvariant state frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (arguments : evalListHOLFinite (runFramesLoopDispatchEntry state pc)
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [runFramesOpcodeExpression] = some [.val (.word (1 : BitVec 64))])
    (clock : 9 ≤ state.clock) (budget : funding.potential ≤ 200000000) :
    ∃ post, evaluateHOLFiniteState state runFramesLoopBody = (none,post) ∧
      HasGasFunding post frame (funding.charge 3) ∧
      post.clock = state.clock - 8 ∧ post.memory (frame + 0) = .word (pc + 1) ∧
      post.locals = state.locals ∧
      (funding.charge 3).used.toNat = funding.used.toNat + 3 := by
  classical
  let dispatchState := runFramesLoopDispatchEntry state pc
  have dispatchInv : GuestFrameInvariant dispatchState frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 := by
    cases inv with
    | mk ev code clock hd b sc cc pcv fm en fe be cb sl scp xd0 xd1 xd2 xd3 xc0 xc1 xc2 xc3
        yd0 yd1 yd2 yd3 yc0 yc1 yc2 yc3 xb yb =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp_all [dispatchState, runFramesLoopDispatchEntry, runFramesDispatchEntry, setVarHOLFinite, HasGasFunding]
  obtain ⟨entry, bodyPost, dispatch, _, funded, pcValue, ticks, _, growth⟩ :=
    opAdd_dispatch_call_progress coeff dispatchState runFramesOpcodeExpression
      (some runFramesExceptionHandler) arguments frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 dispatchInv (by simpa only [dispatchState, runFramesLoopDispatchEntry,
        runFramesDispatchEntry, setVarHOLFinite] using clock) budget inv.enough
  have body := evaluate_runFrames_loop_dispatch state { bodyPost with locals := dispatchState.locals }
    continuation frame pc length active contGlobal inv.ev pendingDomain pendingMemory activeDomain
    activeMemory running (inv.headerDomain 0 (by decide)) inv.pcCell lengthDomain lengthMemory inside
    dispatch rfl
  refine ⟨{ bodyPost with locals := state.locals }, body, ?_, ?_, ?_, rfl, growth⟩
  · change HasGasFunding bodyPost frame (funding.charge 3)
    exact funded
  · change bodyPost.clock = state.clock - 8
    rw [ticks]
    dsimp only [dispatchState, runFramesLoopDispatchEntry, runFramesDispatchEntry, setVarHOLFinite]
  · change bodyPost.memory (frame + 0) = .word (pc + 1)
    exact pcValue

#print axioms runFrames_add_loop_progress
end InitECandidate.Runtime
