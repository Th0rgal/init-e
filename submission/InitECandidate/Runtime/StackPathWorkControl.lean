import InitECandidate.Runtime.StackPathWork
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- Conditional simulation charged only to the branch chosen by source operands. -/
theorem pathWork_if_correct {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp a s (pathWork a s))
    (second : BoundedFlattenProp b s (pathWork b s)) :
    BoundedFlattenProp (.ite cmp reg ri a b) s (pathWork (.ite cmp reg ri a b) s) := by
  have selected := flattenIf_selected_bounded s cmp reg ri a b (pathWork a s) (pathWork b s)
    (fun _ => first) (fun _ => second)
  rw [pathWork]
  simpa only [Nat.add_comm] using selected

/-- Sequence simulation charges the suffix only after an actual NONE return.
The guard is derived from evaluation, not supplied as a new caller premise. -/
theorem pathWork_seq_correct {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (first : BoundedFlattenProp a s (pathWork a s))
    (second : ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (a, s) = (none, middle) →
      BoundedFlattenProp b middle (pathWork b middle)) :
    BoundedFlattenProp (.seq a b) s (pathWork (.seq a b) s) := by
  let returned := StackSemEvaluate.evaluate (a, s)
  let budget := match returned.1 with
    | none => pathWork b returned.2
    | _ => 0
  have next : ∀ (middle : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (a, s) = (none, middle) → BoundedFlattenProp b middle budget := by
    intro middle run
    have reached : budget = pathWork b middle := by simp [budget, returned, run]
    rw [reached]
    exact second middle run
  have composed := flattenSeq_reached_bounded s a b (pathWork a s) budget first next
  intro target result final n l cs bs initial hyps
  apply boundedFlattenConcl_mono (a := pathWork a s + budget) _
    (composed target result final n l cs bs initial hyps)
  rw [pathWork, StackSemEvaluateClock.fixClockEvaluate]
  change pathWork a s + budget ≤ 2 + pathWork a s + budget
  omega

#print axioms pathWork_if_correct
#print axioms pathWork_seq_correct
end InitECandidate.Runtime.StackToLab
