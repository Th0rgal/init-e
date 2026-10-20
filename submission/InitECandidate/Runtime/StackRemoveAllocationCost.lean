import InitECandidate.Runtime.StackRemoveFrameCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem nativeCost_skip {F : Type} (gap : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) .skip source = 0 := by
  simp [stackExecutionCost, nativePriceWithGap]

theorem nativeCost_haltTwo {F : Type} (gap : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (StackRemove.haltInst 2) source ≤ 1 + gap := by
  have constant : instLocalCost (.const 1 2#64) = 1 := by decide_cbv
  have firstBound (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) (.inst (.const 1 2)) s ≤ 1 + gap := by
    simp [stackExecutionCost, nativePriceWithGap, constant]
  have lastBound (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) (.halt 1) s ≤ 0 := by
    simp [stackExecutionCost, nativePriceWithGap]
  simpa only [StackRemove.haltInst, Nat.add_zero] using nativeCost_seq_le gap _ _ (1 + gap) 0 firstBound lastBound source

theorem nativeCost_ite_le {F : Type} (gap : Nat) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (yes no : HolProg 64) (budget : Nat)
    (yesBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) yes s ≤ budget)
    (noBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) no s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (.ite cmp reg operand yes no) source ≤
      (5 + gap) + budget := by
  rw [stackExecutionCost]
  change (5 + gap) + selectedBranchBudget cmp reg operand source _ _ ≤ _
  have hy := yesBound source
  have hn := noBound source
  unfold selectedBranchBudget
  split
  · split <;> omega
  · omega

/-- Non-jump stack allocation pays the actual subtraction, comparison and
possible overflow halt. The final native halt ceiling is charged separately. -/
theorem nativeCost_singleStackAlloc {F : Type} (gap pointer count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.singleStackAlloc false pointer count) source ≤ 7 + 3 * gap := by
  have branch (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :=
    nativeCost_ite_le gap .lower pointer (.reg (pointer + 1)) (StackRemove.haltInst 2) .skip (1 + gap)
      (nativeCost_haltTwo gap) (fun t => (nativeCost_skip gap t).le.trans (Nat.zero_le _)) s
  have bound := nativeCost_seq_le gap _ _ (1 + gap) ((5 + gap) + (1 + gap))
    (fun s => (nativeCost_address_sub gap pointer (StackRemove.wordOffset count) s).le) branch source
  change stackExecutionCost _ (StackRemove.singleStackAlloc false pointer count) source ≤ _ at bound
  omega

/-- Allocation checks are charged once per 255-word chunk, including overflow termination. -/
theorem nativeCost_stackAlloc {F : Type} (gap pointer count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.stackAlloc false pointer count) source ≤ ((count + 254) / 255) * (7 + 3 * gap) := by
  rw [StackRemove.stackAlloc]
  split
  · rename_i zero
    subst count
    simp [stackExecutionCost, nativePriceWithGap]
  · rename_i nonzero
    split
    · exact (nativeCost_singleStackAlloc gap pointer count source).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    · rename_i large
      have bound := nativeCost_seq_le gap
        (StackRemove.singleStackAlloc false pointer StackRemove.maxStackAlloc)
        (StackRemove.stackAlloc false pointer (count - StackRemove.maxStackAlloc)) (7 + 3 * gap)
        (((count - StackRemove.maxStackAlloc + 254) / 255) * (7 + 3 * gap))
        (fun s => nativeCost_singleStackAlloc gap pointer StackRemove.maxStackAlloc s)
        (fun s => nativeCost_stackAlloc gap pointer (count - StackRemove.maxStackAlloc) s) source
      have divEq : (count + 254) / 255 = (count - StackRemove.maxStackAlloc + 254) / 255 + 1 := by
        simp only [StackRemove.maxStackAlloc] at *
        omega
      rw [divEq, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.add_comm] using bound
termination_by count
decreasing_by simp only [StackRemove.maxStackAlloc] at *; omega

/-- Actual compiler output for a frame release retains the size-sensitive bound. -/
theorem nativeCost_comp_stackAlloc {F : Type} (gap pointer count : Nat)
    (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp false bounds pointer (.stackAlloc count)) source ≤
      ((count + 254) / 255) * (7 + 3 * gap) := by
  simpa only [StackRemove.comp] using nativeCost_stackAlloc gap pointer count source


#print axioms nativeCost_stackAlloc
#print axioms nativeCost_comp_stackAlloc
#print axioms nativeCost_ite_le
#print axioms nativeCost_singleStackAlloc
end InitECandidate.Runtime.StackToLab
