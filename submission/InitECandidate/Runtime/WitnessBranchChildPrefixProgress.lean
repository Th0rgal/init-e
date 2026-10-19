import InitECandidate.Runtime.WitnessBranchPreludeReach
import InitECandidate.Runtime.WitnessBranchChildProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual child store and occupancy update, increment and dispatch consume
one child credit and return to resolution on the same stack record. -/
theorem witness_branch_child_prefix_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word branch)))
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (beforeLast : index.toNat < 15) (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2) = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot") = some (.val (.word (index+1))) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      post.memory (top+32#64) = .word (index+1) ∧ post.globals = s.globals ∧
      16-(index+1).toNat < 16-index.toNat := by
  obtain ⟨ready,locals,globals,codeEq,_,_,tailRun,_⟩ := witness_branch_prelude_normal_continuation s post top branch index result
    atTop atBr atIndex atResult code run
  obtain ⟨topPost,slotPost,modePost,counterPost,globalsPost,credit⟩ := witness_branch_child_normal_progress ready post top index
    (by rw [locals]; exact atTop) (by rw [locals]; exact atIndex) beforeLast (codeEq.trans code) tailRun
  exact ⟨topPost,slotPost,modePost,counterPost,globalsPost.trans globals,credit⟩

#print axioms witness_branch_child_prefix_normal_progress
end InitECandidate.Runtime
