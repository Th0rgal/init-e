import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.OriginalFrameErrorCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def frameHaltCallPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left used error : BitVec 64) :=
  sourceWriteWord (sourceWriteWord (sourceWriteWord {state with clock := state.clock - 1}
    (frame + 184) (used + left)) (frame + 64) 0) (frame + 160) error

/-- The real halt call transfers all remaining gas into used, writes the
error word, and restores the caller locals at a cost of one clock. -/
theorem evaluate_frameHalt_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (frame left used error : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word error)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (errorDomain : state.memaddrs (frame + 160))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "frame_halt") [argument]) =
      (none,frameHaltCallPost state frame left used error) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "err",.val (.word error))
  let entry := callEntryStateHOLFinite state callee
  have errorLocal : entry.locals.lookup (ofString "err") = some (.val (.word error)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_source_frameHalt entry frame left used error frameGlobal errorLocal
    leftDomain usedDomain errorDomain leftMemory usedMemory
  have installed : state.code.lookup (ofString "frame_halt") =
      some ([(ofString "err",.one)],sourceFunctionBody Guest.guestFn_frame_halt,.one) := by
    rw [code]; exact originalRuntimeCode_frameHalt_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "frame_halt") (ofString "err")
    (sourceFunctionBody Guest.guestFn_frame_halt) error installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "frame_halt")
    [argument] [.val (.word error)] (sourceFunctionBody Guest.guestFn_frame_halt) callee .one (.val (.word 0))
    (frameHaltPost entry frame left used error) arguments lookup clock body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

theorem frameHaltCallPost_funding {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame error : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (frameHaltCallPost state frame funding.left funding.used error) frame funding.halt := by
  unfold HasGasFunding
  simp [frameHaltCallPost,sourceWriteWord,GasFunding.halt]
  exact memory.2.2

theorem frameHaltCallPost_memory_preserved {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left used error address : BitVec 64)
    (notUsed : address ≠ frame + 184) (notLeft : address ≠ frame + 64)
    (notError : address ≠ frame + 160) :
    (frameHaltCallPost state frame left used error).memory address = state.memory address := by
  unfold frameHaltCallPost sourceWriteWord
  dsimp only
  rw [if_neg notError,if_neg notLeft,if_neg notUsed]

#print axioms frameHaltCallPost_funding
#print axioms frameHaltCallPost_memory_preserved
#print axioms evaluate_frameHalt_call
end InitECandidate.Runtime
