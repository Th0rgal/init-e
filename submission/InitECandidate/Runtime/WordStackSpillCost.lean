import InitECandidate.Runtime.GuestSpillPrices
import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Uniform bounds on reached straight-line fragments compose even if the
first fragment stops. No successful-run or clock allowance is assumed. -/
theorem stackCost_seq_le {F : Type} (price : HolProg 64 → Nat)
    (first second : HolProg 64) (a b : Nat)
    (free : price (.seq first second) = 0)
    (firstBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) first s ≤ a)
    (secondBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) second s ≤ b)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p) (.seq first second) source ≤ a + b := by
  rw [stackExecutionCost_seq]
  simp only [free, Nat.zero_add]
  rcases StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result with
  | none => exact Nat.add_le_add (firstBound source) (secondBound middle)
  | some _ => simpa only [Nat.add_zero] using (firstBound source).trans (Nat.le_add_right a b)

/-- The literal spill loader pays seven per loaded word, rather than a
multiplier depending on the total program or maximum frame size. -/
theorem wordStackLoad_cost {F : Type} (loads : List (Nat × Nat))
    (body : HolProg 64) (budget : Nat)
    (small : ∀ entry ∈ loads, entry.2 ≤ 91)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative loads body) source ≤ 7 * loads.length + budget := by
  induction loads generalizing source with
  | nil => simpa only [WordToStack.Native.wStackLoadNative, List.length_nil, Nat.mul_zero, Nat.zero_add] using bodyBound source
  | cons entry rest ih =>
    rcases entry with ⟨register, offset⟩
    have headSmall : offset ≤ 91 := small (register, offset) (by simp)
    have tailSmall : ∀ entry ∈ rest, entry.2 ≤ 91 := fun entry mem => small entry (by simp [mem])
    have headBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (.stackLoad register offset) s ≤ 7 := by
      intro s
      simp only [stackExecutionCost, guest_spill_load_price register offset headSmall]
      exact Nat.le_refl _
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
      (.stackLoad register offset) (WordToStack.Native.wStackLoadNative rest body)
      7 (7 * rest.length + budget) rfl headBound (fun s => ih tailSmall s) source
    simpa only [WordToStack.Native.wStackLoadNative, List.length_cons, Nat.mul_add,
      Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- A spilled result needs one store; a register result needs none. The
charge is independent of the chosen destination register. -/
theorem wordRegWrite1_cost {F : Type} (g : Nat → HolProg 64)
    (register : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92)
    (bodyBound : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (g r) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wRegWrite1Native g register kf) source ≤
        budget + (if register / 2 < kf.1 then 0 else 7) := by
  simp only [WordToStack.Native.wRegWrite1Native]
  split
  · simpa only [Nat.add_zero] using bodyBound _ source
  · have slot : kf.2.1 - 1 - (register / 2 - kf.1) ≤ 91 := by omega
    apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ budget 7 rfl
      (bodyBound kf.1) (fun s => ?_) source
    simp only [stackExecutionCost, guest_spill_store_price _ _ slot]
    exact Nat.le_refl _

theorem wordRegWrite2_cost {F : Type} (g : Nat → HolProg 64)
    (register : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92)
    (bodyBound : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (g r) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wRegWrite2Native g register kf) source ≤
        budget + (if register / 2 < kf.1 then 0 else 7) := by
  simp only [WordToStack.Native.wRegWrite2Native]
  split
  · simpa only [Nat.add_zero] using bodyBound _ source
  · have slot : kf.2.1 - 1 - (register / 2 - kf.1) ≤ 91 := by omega
    apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ budget 7 rfl
      (bodyBound (kf.1 + 1)) (fun s => ?_) source
    simp only [stackExecutionCost, guest_spill_store_price _ _ slot]
    exact Nat.le_refl _

#print axioms stackCost_seq_le
#print axioms wordStackLoad_cost
#print axioms wordRegWrite1_cost
#print axioms wordRegWrite2_cost
end InitECandidate.Runtime.StackToLab
