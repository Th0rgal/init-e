import InitECandidate.Runtime.WitnessBranchMoreProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual branch advancement before the last child consumes one child credit,
stores the incremented counter, and returns to resolution on the same top. -/
theorem witness_branch_child_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top index : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (beforeLast : index.toNat < 15) (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 4) = (none,post)) :
    ∀ watched : BitVec 64, watched≠top+32#64 → post.memory watched=s.memory watched := by
  have nextNat : (index+1).toNat = index.toNat+1 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+1 < 2^64; omega)]
    rfl
  have comparison : Compiler.Encoders.Asm.wordCmpHOL .less (index+1) (16#64) = true := by
    change Compiler.Encoders.Asm.holAsmSignedLess (index+1) (16#64) = true
    unfold Compiler.Encoders.Asm.holAsmSignedLess
    rw [nextNat]
    simp [show index.toNat+1 < 2^(64-1) by omega,show index.toNat+1 < 16 by omega]
  rw [source_witness_branch_increment] at run
  obtain ⟨selected,incrementRun,tailRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  obtain ⟨value,evaluated,selectedEq⟩ := evaluate_local_assign_normal_value s selected _ _ incrementRun
  have valueEq : value = .val (.word (index+1)) := by
    simpa [evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord] using evaluated.symm
  subst value
  have selectedIndex : selected.locals.lookup (ofString "i") = some (.val (.word (index+1))) := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have selectedTop : selected.locals.lookup (ofString "top") = some (.val (.word top)) := by
    simpa (config := {decide := true}) [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTop
  have condition : @evalHOLExact 64 F _ selected.toExact (fun a => Classical.propDecidable (selected.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.const 16)) = some (.val (.word (1#64))) := by
    simp only [evalHOLExact,selectedIndex]
    change (some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .less (index+1) (16#64) = true then 1 else 0))) : Option (ValueHOL 64)) = _
    rw [comparison]
    rfl
  rw [source_witness_branch_dispatch,evaluateHOLFiniteState_ite,condition] at tailRun
  change evaluateHOLFiniteState selected witnessBranchMore = (none,post) at tailRun
  obtain ⟨topPost,slotPost,modePost,counterPost,globalsPost,memoryPost⟩ := witness_branch_more_normal_progress
    selected post top (index+1) selectedTop selectedIndex (by rw [selectedEq]; exact code) tailRun
  intro watched separate
  exact (memoryPost watched separate).trans (by rw [selectedEq]; rfl)

#print axioms witness_branch_child_normal_memory_frame
end InitECandidate.Runtime
