import InitECandidate.Runtime.WordExecutionCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Structural composition adds only its configured local price and the work
of the actual reached suffix. -/
theorem wordExecutionCost_seq {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordExecutionCost price (.seq first second) source =
      price (.seq first second) source + wordExecutionCost price first source +
        (match evaluate first source with
        | (none, middle) => wordExecutionCost price second middle
        | _ => 0) := by
  rw [wordExecutionCost, fix_clock_evaluate]
  cases run : evaluate first source with
  | mk result middle => cases result <;> rfl

/-- Raising local prices raises the work of the SAME actual execution. No
program/ROM maximum or assumed target bound is used. -/
theorem wordExecutionCost_mono {width : Nat} [NeZero width] {C F : Type}
    (small large : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (le : ∀ p s, small p s ≤ large p s)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    wordExecutionCost small p s ≤ wordExecutionCost large p s := by
  classical
  fun_induction wordExecutionCost small p s <;> (try simp_all +zetaDelta [wordExecutionCost])
  all_goals grind (splits := 40) only

/-- Zero prices do not invent a structural execution overhead. -/
theorem wordExecutionCost_zero {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    wordExecutionCost (fun _ _ => 0) p s = 0 := by
  classical
  fun_induction wordExecutionCost (fun _ _ => 0) p s <;> (try simp_all +zetaDelta [wordExecutionCost])
  all_goals grind (splits := 40) only

/-- Free sequencing in the logical-operation instance. -/
theorem wordLogicalCost_seq {C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordLogicalPrice (.seq first second) s =
      wordExecutionCost wordLogicalPrice first s +
        (match evaluate first s with
        | (none, middle) => wordExecutionCost wordLogicalPrice second middle
        | _ => 0) := by
  simp only [wordExecutionCost_seq, wordLogicalPrice, Nat.zero_add]
  cases run : evaluate first s with
  | mk result middle => cases result <;> rfl

/-- Every actual parallel move pays its word count, rather than one node. -/
theorem wordLogicalCost_move {C F : Type} (priority : Nat) (moves : List (Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordLogicalPrice (.move priority moves) s = 1 + moves.length := by
  simp [wordExecutionCost, wordLogicalPrice]

#print axioms wordExecutionCost_zero
#print axioms wordLogicalCost_seq
#print axioms wordLogicalCost_move
#print axioms wordExecutionCost_seq
#print axioms wordExecutionCost_mono
end InitECandidate.Runtime.FineCost
