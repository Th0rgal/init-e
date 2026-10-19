import InitECandidate.Runtime.WitnessBranchFinishStoresProgress
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_branch_finish_guard_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (prevCell : s.memory top = .word prev)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 4) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
  rw [source_witness_branch_finish_guard] at run
  obtain ⟨ready,normal,storesRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have same := mpt_fail_guard_normal_state s ready _ 9 code normal
  subst ready
  exact witness_branch_finish_stores_normal_progress s post top heap prev atTop atBr prevCell before heapBound storesRun

#print axioms witness_branch_finish_guard_normal_progress
end InitECandidate.Runtime
