import InitECandidate.Runtime.FrameExceptionWork
import InitECandidate.Runtime.GasRefillCall
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete ordinary-error handler body, including refill, halt, return-data
clearing and pending flag. Only the two helper calls consume source clock. -/
theorem evaluate_frameException_error_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame continuation msg gas left used spilled error empty : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (errorLocal : state.locals.lookup (ofString "err") = some (.val (.word error)))
    (emptyGlobal : state.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (notRevert : error ≠ 1)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (spillDomain : state.memaddrs (frame + 192)) (stateDomain : state.memaddrs (frame + 72))
    (pointerDomain : state.memaddrs (frame + 112)) (errorDomain : state.memaddrs (frame + 160))
    (dataDomain : state.memaddrs (frame + 120)) (sizeDomain : state.memaddrs (frame + 128))
    (pendingDomain : state.memaddrs (continuation + 32)) (msgDomain : state.memaddrs (msg + 48))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used)
    (spillMemory : state.memory (frame + 192) = .word spilled)
    (pointerMemory : state.memory (frame + 112) = .word msg)
    (msgMemory : state.memory (msg + 48) = .word gas) (separate : msg + 48 ≠ frame + 64) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_frame_exception) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory (continuation + 32) = .word 1 ∧ post.clock = state.clock - 2 ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs := by
  let refilled := gasRefillCallPost state frame left spilled gas
  let handled := frameExceptionWorkPost refilled frame (left + spilled) used error empty
  let post := emptyLocalsHOLFinite (sourceWriteWord handled (continuation + 32) 1)
  have refill := evaluate_gasRefill_call state frame msg gas left spilled code (by omega) frameGlobal
    leftDomain spillDomain stateDomain pointerDomain msgDomain leftMemory spillMemory pointerMemory msgMemory separate
  have leftAfter : refilled.memory (frame + 64) = .word (left + spilled) := by
    simp [refilled,gasRefillCallPost,sourceWriteWord]
  have usedAfter : refilled.memory (frame + 184) = .word used := by
    simpa [refilled,gasRefillCallPost,sourceWriteWord] using usedMemory
  have work := evaluate_frameException_error_work refilled frame (left + spilled) used error empty code
    (by change state.clock - 1 ≠ 0; omega) frameGlobal errorLocal emptyGlobal notRevert
    leftDomain usedDomain errorDomain dataDomain sizeDomain leftAfter usedAfter
  have tail := evaluate_frameException_pending_tail handled continuation contGlobal pendingDomain
  have body := evaluate_seq_none refill (evaluate_seq_none work tail)
  refine ⟨post,?_,?_,?_,?_,?_,?_⟩
  · rw [source_frameException_body]; exact body
  · simp [post,emptyLocalsHOLFinite,sourceWriteWord]
  · change state.clock - 1 - 1 = state.clock - 2
    omega
  all_goals simp only [post,emptyLocalsHOLFinite,handled,frameExceptionWorkPost,
    frameHaltCallPost,refilled,gasRefillCallPost,sourceWriteWord]

#print axioms evaluate_frameException_error_body
end InitECandidate.Runtime
