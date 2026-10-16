import InitECandidate.Runtime.FrameExceptionBody
import InitECandidate.Runtime.OriginalFrameExceptionCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual ordinary-error handler call finishes in three clocks and marks
    the continuation pending while restoring the caller local environment. -/
theorem evaluate_frameException_error_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (frame continuation msg gas left used spilled error empty : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word error)])
    (code : state.code = originalRuntimeCode) (clock : 3 ≤ state.clock)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (contGlobal : state.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
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
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "frame_exception") [argument]) =
        (none,post) ∧
      post.memory (continuation + 32) = .word 1 ∧ post.clock = state.clock - 3 ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "err",.val (.word error))
  let entry := callEntryStateHOLFinite state callee
  have errorLocal : entry.locals.lookup (ofString "err") = some (.val (.word error)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,body,pending,ticks,globals,postCode,domain⟩ :=
    evaluate_frameException_error_body entry frame continuation msg gas left used spilled error empty
      code (by change 2 ≤ state.clock - 1; omega) frameGlobal contGlobal errorLocal emptyGlobal notRevert
      leftDomain usedDomain spillDomain stateDomain pointerDomain errorDomain dataDomain sizeDomain
      pendingDomain msgDomain leftMemory usedMemory spillMemory pointerMemory msgMemory separate
  have installed : state.code.lookup (ofString "frame_exception") =
      some ([(ofString "err",.one)],sourceFunctionBody Guest.guestFn_frame_exception,.one) := by
    rw [code]; exact originalRuntimeCode_frameException_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "frame_exception") (ofString "err")
    (sourceFunctionBody Guest.guestFn_frame_exception) error installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "frame_exception")
    [argument] [.val (.word error)] (sourceFunctionBody Guest.guestFn_frame_exception) callee .one (.val (.word 0))
    bodyPost arguments lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{bodyPost with locals := state.locals},call,pending,?_,globals,postCode,domain,rfl⟩
  change bodyPost.clock = state.clock - 1 - 2 at ticks
  omega

#print axioms evaluate_frameException_error_call
end InitECandidate.Runtime
