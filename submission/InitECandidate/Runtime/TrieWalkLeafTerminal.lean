import InitECandidate.Runtime.TrieWalkLeafBranchBound
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A return expression either returns its value or reports an expression
error. Neither case falls through to the next source statement. -/
theorem evaluate_return_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.return value)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

/-- A terminal declaration body stays terminal after local restoration;
initializer and shape failures are terminal errors too. -/
theorem evaluate_declaration_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (terminal : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next body).1 ≠ none) :
    (evaluateHOLFiniteState state (.dec name shape initializer body)).1 ≠ none := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact terminal _
    · simp

/-- The exact original leaf branch always exits traversal, including when
its length guard skips comparison or a comparison/load runs out of fuel. -/
theorem evaluate_trieWalk_leaf_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state trieWalkLeafBranch).1 ≠ none := by
  rw [source_trieWalk_leaf_branch]
  apply evaluate_declaration_terminal
  intro next
  rw [source_trieWalk_leaf_after_length]
  apply evaluate_sequence_terminal
  intro finalState
  exact evaluate_return_terminal finalState _

#print axioms evaluate_return_terminal
#print axioms evaluate_declaration_terminal
#print axioms evaluate_trieWalk_leaf_terminal
end InitECandidate.Runtime
