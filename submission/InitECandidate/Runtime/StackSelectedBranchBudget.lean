import InitECandidate.Runtime.StackToLabSelectedIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Charge precisely the branch selected by the actual operand values.
Malformed operands or an undefined comparison cost no branch execution. -/
def selectedBranchBudget {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width)
    (s : StackSemStateFiniteExact width C F) (first second : Nat) : Nat :=
  match StackSemStateOps.getVar reg s,
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
  | some x, some y => match wordSemWordCmp cmp x y with
    | some true => first
    | some false => second
    | none => 0
  | _, _ => 0

theorem selectedBranchBudget_eq {width : Nat} [NeZero width] {C F : Type}
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width)
    (s : StackSemStateFiniteExact width C F) (first second : Nat) (branch : Bool)
    (selected : BranchCondition cmp reg ri s branch) :
    selectedBranchBudget cmp reg ri s first second = if branch then first else second := by
  obtain ⟨x, y, hx, hy, comparison⟩ := selected
  cases branch <;> simp [selectedBranchBudget, hx, hy, comparison]

/-- Asymmetric branch budgets are combined by the actual source condition,
with the same two-instruction local overhead as the original proof. -/
theorem flattenIf_selected_bounded {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width)
    (a b : HolProg width) (firstBudget secondBudget : Nat)
    (first : BranchCondition cmp reg ri s true → BoundedFlattenProp a s firstBudget)
    (second : BranchCondition cmp reg ri s false → BoundedFlattenProp b s secondBudget) :
    BoundedFlattenProp (.ite cmp reg ri a b) s
      (selectedBranchBudget cmp reg ri s firstBudget secondBudget + 2) := by
  apply flattenIf_guarded_bounded s cmp reg ri a b
  · intro chosen
    rw [selectedBranchBudget_eq cmp reg ri s firstBudget secondBudget true chosen]
    exact first chosen
  · intro chosen
    rw [selectedBranchBudget_eq cmp reg ri s firstBudget secondBudget false chosen]
    exact second chosen

#print axioms selectedBranchBudget_eq
#print axioms flattenIf_selected_bounded
end InitECandidate.Runtime.StackToLab
