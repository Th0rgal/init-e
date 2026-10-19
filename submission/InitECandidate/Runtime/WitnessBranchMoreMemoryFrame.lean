import InitECandidate.Runtime.WitnessBranchSource
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
 theorem witness_branch_more_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top index watched : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
    (separate : watched≠top+32) :
    (evaluateHOLFiniteState s witnessBranchMore).2.memory watched=s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched witnessBranchMore := by
    rw [source_witness_branch_more]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨top+32,?_,separate⟩
      simp [evalHOLExact,evalListHOLExact,locals,atTop,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨index,by simpa [evalHOLExact,locals,atIndex] using evaluated.symm⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl
 theorem witness_branch_more_globals_frame : OriginalGlobalsFrame witnessBranchMore := by
  apply originalGlobalsFrame_leaf
  intro watched
  rw [source_witness_branch_more]
  rfl
#print axioms witness_branch_more_word_frame
#print axioms witness_branch_more_globals_frame
end InitECandidate.Runtime
