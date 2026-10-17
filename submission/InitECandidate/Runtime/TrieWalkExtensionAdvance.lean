import InitECandidate.Runtime.TrieWalkBranchProgress
import InitECandidate.Runtime.TrieWalkExtensionBranchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkExtensionAdvance : ProgHOL 64 :=
  match trieWalkExtensionContinuation with | .seq _ tail => tail | _ => .skip

def trieWalkExtensionNodeExpression : ExpHOL 64 :=
  match trieWalkExtensionAdvance with | .seq _ (.assign _ _ value) => value | _ => .const 0

theorem source_trieWalk_extension_advance : trieWalkExtensionAdvance =
    .seq (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.var .local (ofString "sl")]))
      (.assign .local (ofString "node") trieWalkExtensionNodeExpression) := by
  simp only [trieWalkExtensionAdvance,trieWalkExtensionNodeExpression,trieWalkExtensionContinuation,
    trieWalkExtensionComparison,trieWalkExtensionBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_trieWalk_extension_continuation : trieWalkExtensionContinuation =
    .seq (.ite (.cmp .equal (.var .local (ofString "eq2")) (.const 0)) trieWalkEmptyReturn .skip)
      trieWalkExtensionAdvance := by
  simp only [trieWalkExtensionAdvance,trieWalkExtensionContinuation,trieWalkExtensionComparison,
    trieWalkExtensionBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Normal completion of the original extension update advances by its exact
segment length and changes only node/pos locals. -/
theorem evaluate_trieWalk_extension_advance_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (run : evaluateHOLFiniteState state trieWalkExtensionAdvance = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
    (∀ name, name ≠ ofString "node" → name ≠ ofString "pos" → post.locals.lookup name = state.locals.lookup name) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock := by
  let advanced := setVarHOLFinite (ofString "pos") (.val (.word (index + size))) state
  have update : evaluateHOLFiniteState state
      (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.var .local (ofString "sl")])) = (none,advanced) := by
    simp [advanced,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,posLocal,sizeLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
  rw [source_trieWalk_extension_advance,evaluateHOLFiniteState_seq_line780,update] at run
  rcases evaluate_local_assign_control advanced (ofString "node") trieWalkExtensionNodeExpression with ⟨value,assigned⟩ | failed
  · change evaluateHOLFiniteState advanced _ = (none,post) at run
    rw [assigned] at run
    have equal := (Prod.mk.inj run).2
    rw [← equal]
    refine ⟨?_,?_,rfl,rfl,rfl⟩
    · simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "node" ≠ ofString "pos" from by decide]
    · intro name nodeDifferent posDifferent
      simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nodeDifferent,Ne.symm posDifferent]
  · change evaluateHOLFiniteState advanced _ = (none,post) at run
    rw [failed] at run
    cases run

/-- A normal extension continuation cannot take its mismatch return. -/
theorem evaluate_trieWalk_extension_normal_advance {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state trieWalkExtensionContinuation = (none,post)) :
    evaluateHOLFiniteState state trieWalkExtensionAdvance = (none,post) := by
  rw [source_trieWalk_extension_continuation,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · simpa only [evaluateHOLFiniteState_skip] using run
    · have terminal := evaluate_return_terminal state (.rstruct [.const 0,.const 0,.const 0])
      change (evaluateHOLFiniteState state trieWalkEmptyReturn).1 ≠ none at terminal
      cases valueRun : evaluateHOLFiniteState state trieWalkEmptyReturn with
      | mk result middle =>
        rw [valueRun] at terminal run
        cases result with
        | none => exact False.elim (terminal rfl)
        | some result => cases run
  · cases run

theorem evaluate_trieWalk_extension_normal_position {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (run : evaluateHOLFiniteState state trieWalkExtensionContinuation = (none,post)) :
    post.locals.lookup (ofString "pos") = some (.val (.word (index + size))) ∧
    (∀ name, name ≠ ofString "node" → name ≠ ofString "pos" → post.locals.lookup name = state.locals.lookup name) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧ post.clock = state.clock :=
  evaluate_trieWalk_extension_advance_normal state post index size posLocal sizeLocal
    (evaluate_trieWalk_extension_normal_advance state post run)

#print axioms source_trieWalk_extension_advance
#print axioms source_trieWalk_extension_continuation
#print axioms evaluate_trieWalk_extension_advance_normal
#print axioms evaluate_trieWalk_extension_normal_advance
#print axioms evaluate_trieWalk_extension_normal_position
end InitECandidate.Runtime
