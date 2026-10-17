import InitECandidate.Runtime.TrieWalkBranchSyntax
import InitECandidate.Runtime.LocalAssignControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful child selection increments pos exactly once and changes no
memory, globals, or caller locals other than node/pos. -/
theorem evaluate_trieWalk_branch_advance_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state trieWalkBranchAdvance = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + 1))) ∧
    (∀ name, name ≠ ofString "node" → name ≠ ofString "pos" → post.locals.lookup name = state.locals.lookup name) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock := by
  rcases evaluate_local_assign_control state (ofString "node") trieWalkBranchNodeExpression with ⟨value,assigned⟩ | failed
  · let selected := setVarHOLFinite (ofString "node") value state
    have atPos : selected.locals.lookup (ofString "pos") = some (.val (.word index)) := by
      simpa [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "node" ≠ ofString "pos" from by decide] using posLocal
    have advanced : evaluateHOLFiniteState selected
        (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.const 1])) =
        (none,setVarHOLFinite (ofString "pos") (.val (.word (index + 1))) selected) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atPos,wordOpHOL,wordOp,valueIsWord,valueWord,
        lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
    rw [source_trieWalk_branch_advance,evaluateHOLFiniteState_seq_line780,assigned] at run
    change evaluateHOLFiniteState selected _ = (none,post) at run
    rw [advanced] at run
    have equal := (Prod.mk.inj run).2
    rw [← equal]
    refine ⟨?_,?_,rfl,rfl,rfl⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro name nodeDifferent posDifferent
      simp [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nodeDifferent,Ne.symm posDifferent]
  · rw [source_trieWalk_branch_advance,evaluateHOLFiniteState_seq_line780,failed] at run
    cases run

/-- At a branch node a normally completed iteration must take the child path;
the value-return path cannot fall through. -/
theorem evaluate_trieWalk_branch_normal_advance {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    evaluateHOLFiniteState state trieWalkBranchAdvance = (none,post) := by
  rw [source_trieWalk_branch_branch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · simpa only [evaluateHOLFiniteState_skip] using run
    · have terminal := evaluate_trieWalk_branch_value_terminal state
      cases valueRun : evaluateHOLFiniteState state trieWalkBranchValueReturn with
      | mk result middle =>
        rw [valueRun] at terminal run
        cases result with
        | none => exact False.elim (terminal rfl)
        | some result => cases run
  · cases run

/-- Normal branch iterations consume one nibble; this is the progress fact
needed when combining them with extension-node traversal. -/
theorem evaluate_trieWalk_branch_normal_position {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state trieWalkBranchBranch = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + 1))) ∧
    (∀ name, name ≠ ofString "node" → name ≠ ofString "pos" → post.locals.lookup name = state.locals.lookup name) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock :=
  evaluate_trieWalk_branch_advance_normal state post index posLocal (evaluate_trieWalk_branch_normal_advance state post run)

#print axioms evaluate_trieWalk_branch_advance_normal
#print axioms evaluate_trieWalk_branch_normal_advance
#print axioms evaluate_trieWalk_branch_normal_position
end InitECandidate.Runtime
