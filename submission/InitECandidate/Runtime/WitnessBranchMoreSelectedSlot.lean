import InitECandidate.Runtime.WitnessSelectedSlot
import InitECandidate.Runtime.WitnessBranchChildPrefixProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Actual child advancement establishes the selector from its real stored
index. The stage cell is the concrete final metadata retained by the separate
physical-record frame theorem; no synthetic execution is assumed. -/
theorem witness_branch_child_prefix_normal_selected_slot {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word branch)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (beforeLast : index.toNat<15) (code : s.code=originalRuntimeCode)
    (stagePost : post.memory (top+8)=.word (2#64))
    (run : evaluateHOLFiniteState s (witnessBranchAt 2)=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
    post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧ WitnessSelectedSlot post top := by
  obtain ⟨topPost,slotPost,modePost,indexPost,_,_⟩ := witness_branch_child_prefix_normal_progress s post top branch index result
    atTop atBr atResult atIndex beforeLast code run
  have nextNat : (index+1).toNat=index.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64;omega)]
    rfl
  exact ⟨topPost,modePost,Or.inr ⟨stagePost,index+1,indexPost,slotPost,by omega⟩⟩
#print axioms witness_branch_child_prefix_normal_selected_slot
end InitECandidate.Runtime
