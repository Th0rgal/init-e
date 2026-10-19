import InitECandidate.Runtime.WitnessBranchChildMemoryFrame
import InitECandidate.Runtime.WitnessBranchPreludeReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual child delivery changes only its branch child cell, occupancy,
and saved next index before returning to resolution. -/
theorem witness_branch_child_prefix_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br")=some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (beforeLast : index.toNat<15) (code : s.code=originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2)=(none,post)) :
    ∀ watched : BitVec 64, watched≠branch+32+index*8 → watched≠top+40 → watched≠top+32#64 →
      post.memory watched=s.memory watched := by
  obtain ⟨ready,locals,globals,codeEq,domain,endian,tailRun,memory⟩ := witness_branch_prelude_normal_continuation
    s post top branch index result atTop atBr atIndex atResult code run
  have tailFrame := witness_branch_child_normal_memory_frame ready post top index
    (by rw [locals]; exact atTop) (by rw [locals]; exact atIndex) beforeLast (codeEq.trans code) tailRun
  intro watched notChild notOcc notIndex
  exact (tailFrame watched notIndex).trans (memory watched notChild notOcc)

#print axioms witness_branch_child_prefix_normal_memory_frame
end InitECandidate.Runtime
