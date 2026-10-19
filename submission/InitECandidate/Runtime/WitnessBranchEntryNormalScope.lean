import InitECandidate.Runtime.WitnessBranchSource
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.WitnessExtensionProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Exact normal branch entry: the real br/i declarations restore only their
own locals. Every other final local, memory and global is the body's output. -/
theorem witness_branch_entry_normal_scope {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word branch)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (run : evaluateHOLFiniteState s witnessUnwindBranch = (none,post)) :
    let entered := setVarHOLFinite (ofString "i") (.val (.word index))
      (setVarHOLFinite (ofString "br") (.val (.word branch)) s)
    ∃ output, evaluateHOLFiniteState entered (witnessBranchAt 2) = (none,output) ∧
      post.memory=output.memory ∧ post.globals=output.globals ∧
      (∀ name, name ≠ ofString "i" → name ≠ ofString "br" →
        post.locals.lookup name=output.locals.lookup name) := by
  change evaluateHOLFiniteState s (witnessBranchAt 0) = (none,post) at run
  rw [source_witness_branch_entry] at run
  obtain ⟨br,outer,brInit,outerRun,postEq⟩ := evaluate_dec_normal_scope s post _ _ _ _ run
  have brValue : br = .val (.word branch) := by
    have evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 16])) = some (.val (.word branch)) := by
      simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,branchReadable,branchCell]
    exact Option.some.inj (brInit.symm.trans evaluated)
  subst br
  let first := setVarHOLFinite (ofString "br") (.val (.word branch)) s
  obtain ⟨i,output,iInit,bodyRun,outerEq⟩ := evaluate_dec_normal_scope first outer _ _ _ _ outerRun
  have firstTop : first.locals.lookup (ofString "top")=some (.val (.word top)) := by
    simpa (config := {decide := true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTop
  have iValue : i = .val (.word index) := by
    have evaluated : @evalHOLExact 64 F _ first.toExact (fun a => Classical.propDecidable (first.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 32])) = some (.val (.word index)) := by
      simp [evalHOLExact,evalListHOLExact,firstTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,show first.memaddrs (top+32#64) from indexReadable,
        show first.memory (top+32#64)=.word index from indexCell]
    exact Option.some.inj (iInit.symm.trans evaluated)
  subst i
  refine ⟨output,bodyRun,?_,?_,?_⟩
  · rw [postEq,outerEq]
  · rw [postEq,outerEq]
  · intro name notI notBr
    rw [postEq,outerEq]
    change (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq output.locals _) _).lookup name = _
    rw [restore_other_local _ _ _ _ notBr,restore_other_local _ _ _ _ notI]
#print axioms witness_branch_entry_normal_scope
end InitECandidate.Runtime
