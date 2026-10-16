import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.If

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

/-- The original RawCall simulation conclusion, retaining an explicit upper
bound on its existential extra clock and its timeout/stack-overflow exceptions. -/
def BoundedSimulationResult {width : Nat} [NeZero width] {C F : Type}
    (compiled : HolProg width) (info : Spt Nat)
    (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (budget : Nat := 0) : Prop :=
  ∃ clock, clock ≤ budget ∧ ∃ targetState stackSpace,
    stateRel info post targetState ∧
    StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + clock}) =
      (result, {targetState with stackSpace := stackSpace}) ∧
    (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
      stackSpace = targetState.stackSpace)

theorem BoundedSimulationResult.mono {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {info : Spt Nat} {target post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)} {a b : Nat}
    (run : BoundedSimulationResult p info target post result a) (bound : a ≤ b) :
    BoundedSimulationResult p info target post result b := by
  obtain ⟨clock, le, state, space, relation, evaluated, exception⟩ := run
  exact ⟨clock, Nat.le_trans le bound, state, space, relation, evaluated, exception⟩

theorem BoundedSimulationResult.forget {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {info : Spt Nat} {target post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)} {budget : Nat}
    (run : BoundedSimulationResult p info target post result budget) :
    IfCase.SimulationResult p info target post result := by
  obtain ⟨clock, _, state, space, relation, evaluated, exception⟩ := run
  exact ⟨clock, state, space, relation, evaluated, exception⟩

/-- Package a same-clock evaluator transport without discarding its zero bound. -/
theorem unchanged_pair {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (info : Spt Nat)
    (target post final : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (compEq : comp info p = p) (topEq : compTop info p = p)
    (relation : stateRel info post final)
    (run : StackSemEvaluate.evaluate (p, target) = (result, final)) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  have clockSelf : {target with clock := target.clock + 0} = target := by cases target; simp
  have spaceSelf : {final with stackSpace := final.stackSpace} = final := by cases final; rfl
  constructor <;> refine ⟨0, Nat.le_refl 0, final, final.stackSpace, relation, ?_, fun _ => rfl⟩
  · simpa only [clockSelf, spaceSelf, topEq] using run
  · simpa only [clockSelf, spaceSelf, compEq] using run

#print axioms unchanged_pair
end InitECandidate.Runtime.StackRawCall
