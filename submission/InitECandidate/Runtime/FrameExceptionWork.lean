import InitECandidate.Runtime.FrameExceptionPending
import InitECandidate.Runtime.FrameHaltCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def frameExceptionWorkPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left used error empty : BitVec 64) :=
  sourceWriteWord (sourceWriteWord (frameHaltCallPost state frame left used error)
    (frame + 120) empty) (frame + 128) 0

/-- For errors other than REVERT, the actual handler halts the frame and
clears return data, at exactly one call clock after the refill. -/
theorem evaluate_frameException_error_work {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame left used error empty : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (errorLocal : state.locals.lookup (ofString "err") = some (.val (.word error)))
    (emptyGlobal : state.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (notRevert : error ≠ 1)
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (errorDomain : state.memaddrs (frame + 160))
    (dataDomain : state.memaddrs (frame + 120)) (sizeDomain : state.memaddrs (frame + 128))
    (leftMemory : state.memory (frame + 64) = .word left)
    (usedMemory : state.memory (frame + 184) = .word used) :
    evaluateHOLFiniteState state frameExceptionWork =
      (none,frameExceptionWorkPost state frame left used error empty) := by
  classical
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "err")) =
        some (.val (.word error)) := errorLocal
  unfold frameExceptionWork
  rw [evaluate_loaded_word_ite state (.var .local (ofString "err")) error 1 .notEqual guard]
  have notRevertLiteral : error ≠ (1#64) := notRevert
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual error 1 = true := by
    simp [Compiler.Encoders.Asm.wordCmpHOL,notRevertLiteral]
  rw [if_pos flag]
  have halt := evaluate_frameHalt_call state (.var .local (ofString "err")) frame left used error
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,errorLocal]) code clock frameGlobal
    leftDomain usedDomain errorDomain leftMemory usedMemory
  let halted := frameHaltCallPost state frame left used error
  let stored := sourceWriteWord halted (frame + 120) empty
  have data : evaluateHOLFiniteState halted
      (.store (fundingAddress 120) (.var .global (ofString "evm_empty"))) = (none,stored) :=
    evaluate_store_word halted (frame + 120) empty _ _
      (eval_fundingAddress halted frame 120 frameGlobal) emptyGlobal dataDomain
  have size : evaluateHOLFiniteState stored (.store (fundingAddress 128) (.const 0)) =
      (none,frameExceptionWorkPost state frame left used error empty) :=
    evaluate_store_word stored (frame + 128) 0 _ _
      (eval_fundingAddress stored frame 128 frameGlobal) (by rfl) sizeDomain
  exact evaluate_seq_none halt (evaluate_seq_none data size)

/-- REVERT records the error without consuming the remaining regular gas. -/
theorem evaluate_frameException_revert_work {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (errorLocal : state.locals.lookup (ofString "err") = some (.val (.word 1)))
    (errorDomain : state.memaddrs (frame + 160)) :
    evaluateHOLFiniteState state frameExceptionWork = (none,sourceWriteWord state (frame + 160) 1) := by
  unfold frameExceptionWork
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "err")) =
        some (.val (.word (1#64))) := errorLocal
  rw [evaluate_loaded_word_ite state (.var .local (ofString "err")) 1 1 .notEqual loaded]
  simp only [Compiler.Encoders.Asm.wordCmpHOL]
  exact evaluate_store_word state (frame + 160) 1 _ _
    (eval_fundingAddress state frame 160 frameGlobal) errorLocal errorDomain

#print axioms evaluate_frameException_error_work
#print axioms evaluate_frameException_revert_work
end InitECandidate.Runtime
