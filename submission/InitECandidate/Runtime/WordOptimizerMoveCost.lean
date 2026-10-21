import InitECandidate.Runtime.WordRefinedLocalPrice
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordInst

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

/-- Removing shadowed association-list bindings cannot introduce moves. -/
theorem anub_length_le {α β : Type} [DecidableEq α]
    (moves : List (α × β)) (seen : List α) :
    (anub moves seen).length ≤ moves.length := by
  induction moves generalizing seen with
  | nil => simp [anub]
  | cons pair rest ih =>
    rcases pair with ⟨destination, source⟩
    simp only [anub]
    split
    · exact (ih seen).trans (by simp)
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih (destination :: seen))

/-- Unreachable-code removal composes adjacent parallel assignments. The
number of input pairs is additive even when their scheduler cycles change. -/
theorem mergeMoves_length_le (first second : List (Nat × Nat)) :
    (WordUnreach.mergeMoves first second).length ≤ first.length + second.length := by
  unfold WordUnreach.mergeMoves
  exact (anub_length_le _ _).trans (by simp [Nat.add_comm])

/-- Physical renaming can create or remove scheduler cycles. Two emitted
copies per input pair is still a uniform bound, including coalesced copies. -/
theorem renamed_parallel_moves_cost_le (rename : Nat → Nat)
    (moves : List (Nat × Nat)) :
    12 * (Parmove.parmove
      (moves.map (fun move => (rename move.1 / 2, rename move.2 / 2)))).length ≤
      24 * moves.length := by
  have bound := InitECandidate.Runtime.parmove_length_le
    (moves.map (fun move => (rename move.1 / 2, rename move.2 / 2)))
  simp only [List.length_map] at bound
  omega

/-- Native move cost after both merging and renaming. This does not assume
that the exact scheduler length is monotone under either optimization. -/
theorem merged_parallel_moves_cost_le (rename : Nat → Nat)
    (first second : List (Nat × Nat)) :
    12 * (Parmove.parmove
      ((WordUnreach.mergeMoves first second).map
        (fun move => (rename move.1 / 2, rename move.2 / 2)))).length ≤
      24 * first.length + 24 * second.length := by
  have scheduled := renamed_parallel_moves_cost_le rename (WordUnreach.mergeMoves first second)
  have merged := mergeMoves_length_le first second
  omega

/-- The bound applies to the actual canonical execution counter for a merged
Move, rather than merely to a syntactic node-count model. -/
theorem merged_move_execution_cost_le {C F : Type}
    (source : WordSemStateFiniteExact 64 C F) (priority : Nat)
    (first second : List (Nat × Nat)) :
    wordExecutionCost refinedWordLocalPrice
      (.move priority (WordUnreach.mergeMoves first second)) source ≤
      24 * first.length + 24 * second.length := by
  simpa only [wordExecutionCost, refinedWordLocalPrice, refinedWordStackLeafBudget, id_eq]
    using merged_parallel_moves_cost_le id first second

/-- RISC-V disables three-to-two conversion. The entire actual run and its
executed cost are unchanged, for arbitrary states including indirect calls. -/
theorem disabled_threeToTwo_execution {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (program : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (WordInst.threeToTwoRegProg false program) source =
      WordSemStateFiniteExact.evaluate program source ∧
    wordExecutionCost price (WordInst.threeToTwoRegProg false program) source =
      wordExecutionCost price program source := by
  exact ⟨rfl, rfl⟩

#print axioms merged_move_execution_cost_le
#print axioms disabled_threeToTwo_execution
end InitECandidate.Runtime.FineCost
