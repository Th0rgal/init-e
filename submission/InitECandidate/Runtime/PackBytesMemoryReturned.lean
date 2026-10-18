import InitECandidate.Runtime.PackBytesMemoryBound
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem packBytes_memory_globals_frame : OriginalGlobalsFrame (packBytesAt 2) := by
  rw [source_packBytes_copy,source_packBytes_zero]
  exact originalGlobalsFrame_sequence _ _ (memcpy_call_globals_frame _)
    (originalGlobalsFrame_sequence _ _ (memzero_call_globals_frame _) (originalGlobalsFrame_leaf _ (by intro watched; rfl)))

theorem packBytes_memory_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buf count : BitVec 64) (value : ValueHOL 64)
    (hb : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hc : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (packBytesAt 2) = (some (.returned value),post)) :
    value = .rStruct [.val (.word buf),.val (.word count)] ∧ post.globals = state.globals := by
  have globals := packBytes_memory_globals_frame state code
  rw [run] at globals
  rw [source_packBytes_copy] at run
  obtain ⟨middle,copy,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have kept (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments) rfl state
      (by rw [copy]; exact Or.inl rfl)
    simpa only [copy] using frame
  rw [source_packBytes_zero] at tail
  obtain ⟨ready,zero,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) middle v) tail
  have keptAgain (key : MlS) : ready.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memzero") packBytesZeroArguments) rfl middle
      (by rw [zero]; exact Or.inl rfl)
    rw [zero] at frame
    exact frame.trans (kept key)
  have atBuf := (keptAgain _).trans hb
  have atCount := (keptAgain _).trans hc
  rw [evaluateHOLFiniteState_return] at returned
  simp [evalHOLExact,evalListHOLExact,atBuf,atCount,shapeOfHOLExact,sizeOfShapeWithContextHOL] at returned
  exact ⟨returned.1.symm,globals⟩

#print axioms packBytes_memory_globals_frame
#print axioms packBytes_memory_returned
end InitECandidate.Runtime
