import InitECandidate.Runtime.WordStackLoadRunCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.If
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

/-- A reached test costs eleven, plus exactly its selected branch. -/
theorem stackCost_ite_selected {F : Type} (comparison : Cmp) (register : Nat)
    (operand : HolRegImm 64) (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (x y : WordLocW 64) (value : Bool)
    (left : StackSemStateOps.getVar register source = some x)
    (right : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (compared : wordSemWordCmp comparison x y = some value) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (.ite comparison register operand first second) source =
      11 + stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (if value then first else second) source := by
  rw [stackExecutionCost.eq_2]
  have select := selectedBranchBudget_eq comparison register operand source
    (stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) first source)
    (stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) second source)
    value ⟨x, y, left, right, compared⟩
  rw [select]
  cases value <;> rfl

/-- A load-and-test prefix charges each actual spill load and then the
selected continuation at the exact state established by those loads. -/
theorem wordStackLoad_condition_cost {F : Type} (loads : List (Nat × Nat))
    (comparison : Cmp) (register : Nat) (operand : HolRegImm 64)
    (first second : HolProg 64)
    (source loaded : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (x y : WordLocW 64) (value : Bool)
    (small : ∀ entry ∈ loads, entry.2 ≤ 91)
    (run : StackSemEvaluate.evaluate (WordToStack.Native.wStackLoadNative loads .skip, source) =
      (none, loaded))
    (left : StackSemStateOps.getVar register loaded = some x)
    (right : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) loaded = some y)
    (compared : wordSemWordCmp comparison x y = some value) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative loads (.ite comparison register operand first second)) source ≤
      7 * loads.length + 11 +
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (if value then first else second) loaded := by
  have bound := wordStackLoad_cost_run loads (.ite comparison register operand first second)
    source loaded small run
  rw [stackCost_ite_selected comparison register operand first second loaded x y value left right compared] at bound
  simpa only [Nat.add_assoc] using bound

#print axioms stackCost_ite_selected
#print axioms wordStackLoad_condition_cost
end InitECandidate.Runtime.StackToLab
