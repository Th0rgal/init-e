import InitECandidate.Runtime.WitnessBranchSource
import InitECandidate.Runtime.WitnessExtensionStoresProgress
import InitECandidate.Runtime.WordStoreNormalMemory
import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual branch continuation saves the next child index, schedules that
slot for resolution, retains the top and changes no other memory cell. -/
theorem witness_branch_more_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top index : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessBranchMore = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot") = some (.val (.word index)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      post.memory (top+32#64) = .word index ∧ post.globals = s.globals ∧
      ∀ watched : BitVec 64, watched ≠ top+32#64 → post.memory watched = s.memory watched := by
  have globalFrame : OriginalGlobalsFrame witnessBranchMore := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_witness_branch_more]
    rfl
  have globals := globalFrame s code
  rw [run] at globals
  rw [source_witness_branch_more] at run
  obtain ⟨stored,storeRun,storeLocals,tailRun⟩ := evaluate_store_sequence_normal s post _ _ _ run
  have cells := evaluate_word_store_normal_memory s stored _ _ (top+32#64) index
    (by simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atIndex]) storeRun
  have memory := evaluate_readOnly_memory
    (.seq (.assign .local (ofString "slot") (.var .local (ofString "i")))
      (.assign .local (ofString "mode") (.const 2))) rfl stored
  rw [tailRun] at memory
  obtain ⟨slotted,slotRun,modeRun⟩ := witness_extension_sequence_normal_parts stored post _ _ tailRun
  obtain ⟨value,evaluated,slottedEq⟩ := evaluate_local_assign_normal_value stored slotted _ _ slotRun
  have valueEq : value = .val (.word index) := by simpa [evalHOLExact,storeLocals,atIndex] using evaluated.symm
  subst value
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value slotted post _ _ modeRun
  have valueEq : value = .val (.word (2#64)) := by simpa [evalHOLExact] using evaluated.symm
  subst value
  refine ⟨?_,?_,?_,?_,globals,?_⟩
  · simp (config := {decide := true}) [postEq,slottedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,storeLocals,atTop]
  · simp (config := {decide := true}) [postEq,slottedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [postEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [memory]; exact cells.1
  · intro watched different
    rw [memory]; exact cells.2 watched different

#print axioms witness_branch_more_normal_progress
end InitECandidate.Runtime
