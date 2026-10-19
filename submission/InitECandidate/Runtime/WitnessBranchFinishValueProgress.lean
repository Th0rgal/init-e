import InitECandidate.Runtime.WitnessBranchFinishGuardProgress
import InitECandidate.Runtime.WitnessBranchValueFrame
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual value caching, occupancy rejection and final cache/pop code preserve
the saved link and deliver the original branch node on normal completion. -/
theorem witness_branch_finish_value_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev kind pointer length consumed : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (atValue : s.locals.lookup (ofString "bv") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (prevCell : s.memory top = .word prev)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 3) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
  rw [source_witness_branch_value_sequence] at run
  obtain ⟨ready,normal,guardRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have memory := witness_branch_value_update_word_frame s heap kind pointer length consumed top atBr atValue heapBound before
  rw [normal] at memory
  have keep (name : MlS) (supported : avoidsLocal name witnessBranchValueUpdate = true) :
      ready.locals.lookup name = s.locals.lookup name := by
    have frame := evaluate_avoidsLocal_flowing name witnessBranchValueUpdate supported s (by rw [normal]; exact Or.inl rfl)
    rw [normal] at frame
    exact frame
  have topKept := keep (ofString "top") (by rw [source_witness_branch_value_update,source_witness_branch_value_stores]; decide)
  have brKept := keep (ofString "br") (by rw [source_witness_branch_value_update,source_witness_branch_value_stores]; decide)
  have modeKept := keep (ofString "mode") (by rw [source_witness_branch_value_update,source_witness_branch_value_stores]; decide)
  have metadata := evaluateHOLFiniteState_metadata s witnessBranchValueUpdate
  rw [normal] at metadata
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_finish_guard_normal_progress ready post top heap prev
    (topKept.trans atTop) (brKept.trans atBr) (memory.trans prevCell) before heapBound (metadata.1.trans code) guardRun
  exact ⟨topPost,resultPost,modePost.trans modeKept,cellPost.trans memory⟩

#print axioms witness_branch_finish_value_normal_progress
end InitECandidate.Runtime
