import InitECandidate.Runtime.CrepExpressionWork
import Flapjack.Pancake.CrepToLoop.ContextExact
namespace InitECandidate.Runtime.FineCost
open Flapjack

mutual
  def loopValueWork : HolLoopExp 64 → Nat
    | .topAddr => 5
    | .load address => 1 + loopValueWork address
    | .op _ args => 1 + loopValuesWork args
    | .shift _ left right => 1 + loopValueWork left + loopValueWork right
    | _ => 1
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def loopValuesWork : List (HolLoopExp 64) → Nat
    | [] => 0
    | head :: tail => loopValueWork head + loopValuesWork tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Native cap of evaluating a Loop expression into a destination, from the
  checked `WordToStack` caps at gap 6: var 14, constant 19, global or heap
  lookup 14, load 21 + address, binary operator 28 per extra operand +
  operands, shift 32 + operands (an immediate shift 25 + operand). -/
  def loopNativeValue : HolLoopExp 64 → Nat
    | .const _ => 19
    | .var _ => 14
    | .lookup _ => 14
    | .baseAddr => 14
    | .topAddr => 28 + 14 + (25 + 14)
    | .load address => 21 + loopNativeValue address
    | .op _ args => 28 * (args.length - 1) + 19 * (1 - (args.length - 1)) + loopNativeValues args
    | .shift _ left right => 32 + loopNativeValue left + loopNativeValue right
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def loopNativeValues : List (HolLoopExp 64) → Nat
    | [] => 0
    | head :: tail => loopNativeValue head + loopNativeValues tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Local expression-generated code allowance. Unsupported control flow
  returns none; loops and calls cannot be silently assigned a finite cost.
  Conditional branches use their larger allowance, not their sum. -/
  def loopExpressionCodeWork : HolLoopProg 64 → Option Nat
    | .skip => some 0
    | .assign _ value => some (loopNativeValue value)
    | .arith _ => some 43
    | .load32 _ _ | .loadByte _ _ => some 35
    | .seq first second => do
        let a ← loopExpressionCodeWork first
        let b ← loopExpressionCodeWork second
        pure (a + b)
    | .ite _ _ _ yes no _ => do
        let a ← loopExpressionCodeWork yes
        let b ← loopExpressionCodeWork no
        pure (37 + max a b)
    | _ => none
  termination_by p => sizeOf p

  def loopExpressionCodesWork : List (HolLoopProg 64) → Option Nat
    | [] => some 0
    | head :: tail => do
        let a ← loopExpressionCodeWork head
        let b ← loopExpressionCodesWork tail
        pure (a + b)
  termination_by ps => sizeOf ps
end

theorem loopExpressionCodesWork_append (left right : List (HolLoopProg 64)) :
    loopExpressionCodesWork (left ++ right) = (do
      let a ← loopExpressionCodesWork left
      let b ← loopExpressionCodesWork right
      pure (a + b)) := by
  induction left with
  | nil => simp [loopExpressionCodesWork]
  | cons head tail ih =>
    simp only [List.cons_append, loopExpressionCodesWork, ih]
    cases loopExpressionCodeWork head <;> cases loopExpressionCodesWork tail <;>
      cases loopExpressionCodesWork right <;> simp [Nat.add_assoc]

/-- Includes the residual expression as well as the emitted statements. A
clock-only accounting would lose both assignment and memory-access work. -/
def crepToLoopExpansionWork (context : CrepToLoopContextExact) (tmp : Nat)
    (live : NumSet) (e : CrepExpHOL 64) : Option Nat :=
  let compiled := compileExpHOLExact context tmp live e
  (loopExpressionCodesWork compiled.1).map (fun cost => cost + loopNativeValue compiled.2.1)

/-- Scalar loadByte adds a memory operation and a residual variable. -/
theorem crepToLoop_loadByte_expansion (context : CrepToLoopContextExact) (tmp : Nat)
    (live : NumSet) (address : CrepExpHOL 64) :
    crepToLoopExpansionWork context tmp live (.loadByte address) =
      (crepToLoopExpansionWork context tmp live address).map (fun cost => cost + 49) := by
  unfold crepToLoopExpansionWork
  generalize hc : compileExpHOLExact context tmp live address = compiled
  obtain ⟨code, value, next, out⟩ := compiled
  rw [compileExpHOLExact, hc]
  simp only [loopExpressionCodesWork_append, loopExpressionCodesWork,
    loopExpressionCodeWork, loopNativeValue]
  cases loopExpressionCodesWork code <;> simp [Nat.add_assoc] <;> omega

#print axioms crepToLoop_loadByte_expansion

/-- Scalar load32 adds a memory operation and a residual variable. -/
theorem crepToLoop_load32_expansion (context : CrepToLoopContextExact) (tmp : Nat)
    (live : NumSet) (address : CrepExpHOL 64) :
    crepToLoopExpansionWork context tmp live (.load32 address) =
      (crepToLoopExpansionWork context tmp live address).map (fun cost => cost + 49) := by
  unfold crepToLoopExpansionWork
  generalize hc : compileExpHOLExact context tmp live address = compiled
  obtain ⟨code, value, next, out⟩ := compiled
  rw [compileExpHOLExact, hc]
  simp only [loopExpressionCodesWork_append, loopExpressionCodesWork,
    loopExpressionCodeWork, loopNativeValue]
  cases loopExpressionCodesWork code <;> simp [Nat.add_assoc] <;> omega

#print axioms crepToLoop_load32_expansion

/-- The comparison materializer evaluates both operands, then performs two
assignments and one branch with a two-unit selected assignment arm and the subsequent lowered tick. -/
theorem comparison_materializer_work (operator : Cmp)
    (first second : List (HolLoopProg 64)) (left right : HolLoopExp 64)
    (condition rightRegister : Nat) (live : NumSet) (a b : Nat)
    (firstCost : loopExpressionCodesWork first = some a)
    (secondCost : loopExpressionCodesWork second = some b) :
    loopExpressionCodesWork
      (progIfHOLExact operator first second left right condition rightRegister live) =
      some (a + b + loopNativeValue left + loopNativeValue right + 56) := by
  unfold progIfHOLExact
  simp only [loopExpressionCodesWork_append, firstCost, secondCost,
    loopExpressionCodesWork, loopExpressionCodeWork, loopNativeValue]
  simp
  omega

#print axioms comparison_materializer_work

end InitECandidate.Runtime.FineCost
