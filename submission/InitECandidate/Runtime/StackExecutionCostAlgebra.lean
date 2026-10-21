import InitECandidate.Runtime.StackExecutionCostProps
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- A coefficient scales each visited local operation once. -/
theorem stackExecutionCost_scale {width : Nat} [NeZero width] {C F : Type}
    (price : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (coefficient : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    stackExecutionCost (fun p s => coefficient * price p s) p s =
      coefficient * stackExecutionCost price p s := by
  induction coefficient with
  | zero => simpa only [Nat.zero_mul] using stackExecutionCost_zero p s
  | succ coefficient ih =>
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, stackExecutionCost_add, ih]

/-- Pointwise compiler prices combine into the same executed-path envelope.
This theorem supplies no unproved local native prices. -/
theorem stackExecutionCost_linear_envelope {width : Nat} [NeZero width] {C F : Type}
    (actual first second : HolProg width → StackSemStateFiniteExact width C F → Nat)
    (a b : Nat) (prices : ∀ p s, actual p s ≤ a * first p s + b * second p s)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    stackExecutionCost actual p s ≤
      a * stackExecutionCost first p s + b * stackExecutionCost second p s := by
  have bound := stackExecutionCost_mono actual
    (fun p s => a * first p s + b * second p s) prices p s
  simpa only [stackExecutionCost_add, stackExecutionCost_scale] using bound

#print axioms stackExecutionCost_scale
#print axioms stackExecutionCost_linear_envelope
end InitECandidate.Runtime.StackToLab
