import InitECandidate.Runtime.ReachesTerminalBound
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Close an actual bounded prefix with its bounded continuation. -/
theorem RunBounded.ofReaches {F : Type} {s : PanSemStateFiniteExact 64 F} {program tail : ProgHOL 64}
    {P : PanSemStateFiniteExact 64 F → Prop} {prefixCost tailCost : Nat}
    (budget : prefixCost + tailCost ≤ s.clock) (prefixRun : Reaches s program P prefixCost tail)
    (tailBound : ∀ next, P next → tailCost ≤ next.clock → RunBounded next tail tailCost) :
    RunBounded s program (prefixCost + tailCost) :=
  evaluate_reaches_terminal_bounded s program tail P prefixCost tailCost budget prefixRun tailBound

/-- Compose prefixes while making the remaining clock budget available. -/
theorem reaches_trans_budget {F : Type} (s : PanSemStateFiniteExact 64 F) (program middle tail : ProgHOL 64)
    (P Q : PanSemStateFiniteExact 64 F → Prop) (prefixCost tailCost : Nat)
    (budget : prefixCost + tailCost ≤ s.clock) (prefixRun : Reaches s program P prefixCost middle)
    (tailRun : ∀ next, P next → tailCost ≤ next.clock → Reaches next middle Q tailCost tail) :
    Reaches s program Q (prefixCost + tailCost) tail := by
  have annotated : Reaches s program (fun next => P next ∧ s.clock ≤ next.clock + prefixCost) prefixCost middle := by
    rcases prefixRun with ⟨next,facts,spent,remaining,agreement⟩ | aborted
    · exact Or.inl ⟨next,⟨facts,spent⟩,spent,remaining,agreement⟩
    · exact Or.inr aborted
  exact reaches_trans s program middle tail _ Q prefixCost tailCost annotated
    (fun next ⟨facts,spent⟩ => tailRun next facts (by omega))

#print axioms RunBounded.ofReaches
#print axioms reaches_trans_budget
end InitECandidate.Runtime
