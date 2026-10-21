import InitECandidate.Runtime.WordStackSpillCost
import InitECandidate.Runtime.StackRefinedRemovalPrice
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target

theorem guest_spill_load_refined_price (reg count : Nat) (small : count ≤ 91) :
    refinedRemovalLocalPrice 6 riscvConfig.addrOffset (.stackLoad reg count) = 6 := by
  simp only [refinedRemovalLocalPrice, riscv_spill_offset count small, ↓reduceIte]

theorem guest_spill_store_refined_price (reg count : Nat) (small : count ≤ 91) :
    refinedRemovalLocalPrice 6 riscvConfig.addrOffset (.stackStore reg count) = 6 := by
  simp only [refinedRemovalLocalPrice, riscv_spill_offset count small, ↓reduceIte]

/-- The literal spill loader pays six per loaded word, rather than a
multiplier depending on the total program or maximum frame size. -/
theorem wordStackLoad_refined_cost {F : Type} (loads : List (Nat × Nat))
    (body : HolProg 64) (budget : Nat)
    (small : ∀ entry ∈ loads, entry.2 ≤ 91)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative loads body) source ≤ 6 * loads.length + budget := by
  induction loads generalizing source with
  | nil => simpa only [WordToStack.Native.wStackLoadNative, List.length_nil, Nat.mul_zero, Nat.zero_add] using bodyBound source
  | cons entry rest ih =>
    rcases entry with ⟨register, offset⟩
    have headSmall : offset ≤ 91 := small (register, offset) (by simp)
    have tailSmall : ∀ entry ∈ rest, entry.2 ≤ 91 := fun entry mem => small entry (by simp [mem])
    have headBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
          (.stackLoad register offset) s ≤ 6 := by
      intro s
      simp only [stackExecutionCost, guest_spill_load_refined_price register offset headSmall]
      exact Nat.le_refl _
    have bound := stackCost_seq_le (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
      (.stackLoad register offset) (WordToStack.Native.wStackLoadNative rest body)
      6 (6 * rest.length + budget) rfl headBound (fun s => ih tailSmall s) source
    simpa only [WordToStack.Native.wStackLoadNative, List.length_cons, Nat.mul_add,
      Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- A spilled result needs one store; a register result needs none. The
charge is independent of the chosen destination register. -/
theorem wordRegWrite1_refined_cost {F : Type} (g : Nat → HolProg 64)
    (register : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92)
    (bodyBound : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p) (g r) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wRegWrite1Native g register kf) source ≤
        budget + (if register / 2 < kf.1 then 0 else 6) := by
  simp only [WordToStack.Native.wRegWrite1Native]
  split
  · simpa only [Nat.add_zero] using bodyBound _ source
  · have slot : kf.2.1 - 1 - (register / 2 - kf.1) ≤ 91 := by omega
    apply stackCost_seq_le (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) _ _ budget 6 rfl
      (bodyBound kf.1) (fun s => ?_) source
    simp only [stackExecutionCost, guest_spill_store_refined_price _ _ slot]
    exact Nat.le_refl _

theorem wordRegWrite2_refined_cost {F : Type} (g : Nat → HolProg 64)
    (register : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92)
    (bodyBound : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p) (g r) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wRegWrite2Native g register kf) source ≤
        budget + (if register / 2 < kf.1 then 0 else 6) := by
  simp only [WordToStack.Native.wRegWrite2Native]
  split
  · simpa only [Nat.add_zero] using bodyBound _ source
  · have slot : kf.2.1 - 1 - (register / 2 - kf.1) ≤ 91 := by omega
    apply stackCost_seq_le (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) _ _ budget 6 rfl
      (bodyBound (kf.1 + 1)) (fun s => ?_) source
    simp only [stackExecutionCost, guest_spill_store_refined_price _ _ slot]
    exact Nat.le_refl _

#print axioms guest_spill_load_refined_price
#print axioms guest_spill_store_refined_price
#print axioms wordStackLoad_refined_cost
#print axioms wordRegWrite1_refined_cost
#print axioms wordRegWrite2_refined_cost
end InitECandidate.Runtime.StackToLab
