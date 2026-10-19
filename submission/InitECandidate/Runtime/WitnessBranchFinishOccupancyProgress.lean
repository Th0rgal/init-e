import InitECandidate.Runtime.WitnessBranchFinishValueProgress
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_branch_finish_occupancy_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev kind pointer length consumed : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (atValue : s.locals.lookup (ofString "bv") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (prevCell : s.memory top = .word prev)
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 2) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
  rw [source_witness_branch_finish_occupancy] at run
  obtain ⟨value,output,_,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post (ofString "occ") .one _ (witnessBranchFinishAt 3) run
  let entered := setVarHOLFinite (ofString "occ") value s
  have topEntry : entered.locals.lookup (ofString "top") = s.locals.lookup (ofString "top") := by
    simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have brEntry : entered.locals.lookup (ofString "br") = s.locals.lookup (ofString "br") := by
    simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have valueEntry : entered.locals.lookup (ofString "bv") = s.locals.lookup (ofString "bv") := by
    simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have modeEntry : entered.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") := by
    simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨topPost,resultPost,modePost,cellPost⟩ := witness_branch_finish_value_normal_progress entered output
    top heap prev kind pointer length consumed (topEntry.trans atTop) (brEntry.trans atBr)
    (valueEntry.trans atValue) prevCell before heapBound code bodyRun
  have otherLocal (name : MlS) (different : name ≠ ofString "occ") :
      post.locals.lookup name = output.locals.lookup name := by
    rw [postEq]
    exact restore_other_local _ _ name _ different
  exact ⟨(otherLocal _ (by decide)).trans topPost,(otherLocal _ (by decide)).trans resultPost,
    (otherLocal _ (by decide)).trans (modePost.trans modeEntry),by rw [postEq]; exact cellPost⟩

#print axioms witness_branch_finish_occupancy_normal_progress
end InitECandidate.Runtime
