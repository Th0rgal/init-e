import InitECandidate.Runtime.StackPathWorkLeaves
import InitECandidate.Runtime.StackPathWorkJumps
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- Constructor assembly with a concrete source-derived budget at every
recursive evaluation, including calls and dynamically installed code. -/
theorem pathWork_of_ih {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F)
    (ih : ∀ (p' : HolProg width) (s' : StackSemStateFiniteExact width C F),
      MeasureLt p' s' prog s → BoundedFlattenProp p' s' (pathWork p' s')) :
    BoundedFlattenProp prog s (pathWork prog s) := by
  cases prog with
  | seq a b =>
    apply pathWork_seq_correct
    · exact ih a s (.inr ⟨rfl, StackSemMeasure.seq_first_size_lt a b⟩)
    · intro middle run
      exact ih b middle (measureLtOfClockLe
        (StackSemEvaluateClock.evaluateClock _ _ _ _ run) (StackSemMeasure.seq_second_size_lt a b))
  | ite cmp r ri a b =>
    exact pathWork_if_correct cmp r ri a b s
      (ih a s (.inr ⟨rfl, StackSemMeasure.if_first_size_lt cmp r ri a b⟩))
      (ih b s (.inr ⟨rfl, StackSemMeasure.if_second_size_lt cmp r ri a b⟩))
  | loop body =>
    apply pathWork_loop_bound
    · exact ih body s (.inr ⟨rfl, StackSemMeasure.loop_body_size_lt body⟩)
    · intro result middle run continuing positive
      apply ih (.loop body) (StackSemStateOps.decClock middle)
      left
      have clockLe := StackSemEvaluateClock.evaluateClock _ _ _ _ run
      simp only [StackSemStateOps.decClock]
      omega
  | call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩
    · exact pathWork_tailCall_bound s dest handler ih
    · exact pathWork_returnCall_bound s rp link l1 l2 dest handler ih
  | jumpLower r1 r2 dest => exact pathWork_jumpLower_bound s r1 r2 dest ih
  | rawCall dest => exact pathWork_rawCall_bound s dest ih
  | _ => apply pathWork_leaf_bound; rfl

/-- Full quantitative stack-to-label simulation: the added label clock is
bounded by a total Nat function of the source program and source state.
This is not yet a uniform numerical bound over challenge inputs. -/
theorem pathWork_correct {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) :
    BoundedFlattenProp prog s (pathWork prog s) :=
  measureLtWf.induction (C := fun a => BoundedFlattenProp a.1 a.2 (pathWork a.1 a.2))
    (prog, s) fun a ih => pathWork_of_ih a.1 a.2 fun p' s' h => ih (p', s') h

#print axioms pathWork_correct
end InitECandidate.Runtime.StackToLab
