import InitECandidate.Runtime.WordStackSpillCost
import InitECandidate.Runtime.RiscVStackImmediateCost
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Literal descending argument copies retain their actual count and order.
An early stop can only remove a suffix of these copies. -/
theorem wordStack_stackMove_cost {F : Type} (count start offset temporary : Nat)
    (body : HolProg 64) (budget : Nat) (fits : count+start+offset ≤ 256)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (stackMoveNative count start offset temporary body) source ≤ 14*count + budget := by
  induction count generalizing start source with
  | zero => simpa only [stackMoveNative, Nat.mul_zero, Nat.zero_add] using bodyBound source
  | succ count ih =>
    have firstBound := fun s => ih (start+1) (by omega) s
    have tailBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (.seq (.stackLoad temporary (start+offset)) (.stackStore temporary start)) s ≤ 14 := by
      intro s
      apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 7 rfl
        (fun state => ?_) (fun state => ?_) s
      · simp only [stackExecutionCost, riscv_stack_load_price temporary (start+offset) (by omega), Nat.le_refl]
      · simp only [stackExecutionCost, riscv_stack_store_price temporary start (by omega), Nat.le_refl]
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
      (stackMoveNative count (start+1) offset temporary body)
      (.seq (.stackLoad temporary (start+offset)) (.stackStore temporary start))
      (14*count+budget) 14 rfl firstBound tailBound source
    simpa only [stackMoveNative, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- Allocating and copying zero stack arguments is free. Every further word
pays at most 25 for allocation and 14 for its load/store pair. -/
theorem wordStack_stackArgs_cost {F : Type} {α β : Type} (dest : Sum α β)
    (argCount : Nat) (kf : Nat × Nat × Nat)
    (frameSmall : kf.2.1 ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount dest argCount kf.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (stackArgsNative dest argCount kf) source ≤
      39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount dest argCount kf.1 := by
  let count := Flapjack.Compiler.Backend.WordToStack.stackArgCount dest argCount kf.1
  have allocation : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.stackAlloc count) s ≤ 25*count := by
    intro s
    by_cases zero : count = 0
    · simp [zero, stackExecutionCost, removalLocalPrice]
    · have bound := guest_frame_alloc_price count argsSmall
      simp only [stackExecutionCost]
      exact bound.trans (by omega)
  have bound := wordStack_stackMove_cost count 0 kf.2.1 kf.1 (.stackAlloc count)
    (25*count) (by dsimp only [count]; omega) allocation source
  change stackExecutionCost _ (stackMoveNative count 0 kf.2.1 kf.1 (.stackAlloc count)) source ≤ 39*count
  omega

#print axioms wordStack_stackMove_cost
#print axioms wordStack_stackArgs_cost
end InitECandidate.Runtime.WordToStack
