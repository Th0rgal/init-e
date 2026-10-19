import InitECandidate.Runtime.MerklePaddingSource
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.PanDiscardReturnMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleFinish_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buf out mark watched : BitVec 64) (value : ValueHOL 64)
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state (merkleizeAt 13) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_merkleFinish] at run
  let arguments : List (ExpHOL 64) := [.var .local (ofString "out"),.var .local (ofString "buf"),.const 32]
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "memcpy") arguments v) run
  have separate := memcpy_interval_separate out (32#64) watched aligned fits outside
  have frame := memcpy_call_normal_memory state middle arguments out buf (32#64) watched
    (by simp [arguments,evalListHOLExact,evalHOLExact,atBuf,atOut]) code
    (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
    (by decide) budget normal
  have kept := evaluate_avoidsLocal_flowing (ofString "mark")
    (.call (some (none,none)) (ofString "memcpy") arguments) rfl state
    (by rw [normal]; exact Or.inl rfl)
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  rw [normal] at kept meta'
  obtain ⟨last,released,memory⟩ := evaluate_discard_then_return_memory middle post (ofString "heap_release")
    [.var .local (ofString "mark")] (.return (.const 0)) value rfl tail
  have marker : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := kept.trans atMark
  have releaseMemory := heapRelease_call_normal_memory middle last (.var .local (ofString "mark")) mark
    (meta'.1.trans code) (by simp [evalListHOLExact,evalHOLExact,marker]) released
  exact (congrFun memory watched).trans ((congrFun releaseMemory watched).trans frame)

#print axioms merkleFinish_returned_memory
end InitECandidate.Runtime
