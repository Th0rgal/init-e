import InitECandidate.Runtime.WordStackInstructionCost
import InitECandidate.Runtime.InstBudget
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

theorem wordStack_inst_cost {F : Type} (instruction : HolInst 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (.inst instruction) source ≤ 22 := by
  cases instruction with
  | skip => simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
  | const rd value =>
    have bound := const_native_length_le rd value
    simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost] using
      Nat.add_le_add_right (bound.trans (by decide : 6 ≤ 16)) 6
  | arith operation => cases operation <;>
      simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
  | mem operation rd address =>
      simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]

/-- Ordered loads and a possibly spilled write retain a charge per actual
operand, followed by the caller's bound on the executed core fragment. -/
theorem wordStack_read_write_cost {F : Type} (loads : List (Nat × Nat))
    (g : Nat → HolProg 64) (dst : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92) (loadsSmall : ∀ entry ∈ loads, entry.2 ≤ 91)
    (core : ∀ n (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (g n) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative loads
        (WordToStack.Native.wRegWrite1Native g dst kf)) source ≤
      7 * loads.length + budget + (if dst / 2 < kf.1 then 0 else 7) := by
  have bound := wordStackLoad_cost loads _
    (budget + (if dst / 2 < kf.1 then 0 else 7)) loadsSmall
    (fun s => wordRegWrite1_cost g dst kf budget small core s) source
  simpa only [Nat.add_assoc] using bound

private theorem read1_write {F : Type} (read dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1
        (WordToStack.Native.wRegWrite1Native (fun n => .inst (g n)) dst kf)) source ≤ 43 := by
  have loads := wordReg1_loads read kf small
  have bound := wordStack_read_write_cost _ _ dst kf 22 small loads.2
    (fun n s => wordStack_inst_cost (g n) s) source
  split_ifs at bound <;> omega

private theorem read2_write {F : Type} (read1 read2 dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (WordToStack.Native.wRegWrite1Native (fun n => .inst (g n)) dst kf)) source ≤ 43 := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have loadsSmall : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStack_read_write_cost _ _ dst kf 22 small loadsSmall
    (fun n s => wordStack_inst_cost (g n) s) source
  simp only [List.length_append] at bound
  split_ifs at bound <;> omega

private theorem read1_only {F : Type} (read : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1
        (.inst instruction)) source ≤ 43 := by
  have loads := wordReg1_loads read kf small
  have bound := wordStackLoad_cost _ _ 22 loads.2 (wordStack_inst_cost instruction) source
  omega

private theorem read2_only {F : Type} (read1 read2 : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (.inst instruction)) source ≤ 43 := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have loadsSmall : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStackLoad_cost _ _ 22 loadsSmall (wordStack_inst_cost instruction) source
  simp only [List.length_append] at bound
  omega

/-- Every literal Word instruction has a small executed-cost bound after
spilling. This is a per-executed-instruction ceiling, not a ROM-size factor. -/
theorem wordInst_cost {F : Type} (instruction : HolInst 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wInstNative instruction kf) source ≤ 43 := by
  cases instruction with
  | skip => exact (wordStack_inst_cost .skip source).trans (by decide)
  | const rd value =>
    have bound := wordRegWrite1_cost (fun n => .inst (.const n value)) rd kf 22 small
      (fun n s => wordStack_inst_cost (.const n value) s) source
    simp only [WordToStack.Native.wInstNative]
    split_ifs at bound <;> omega
  | mem operation rd address =>
    cases address
    cases operation <;> simp only [WordToStack.Native.wInstNative]
    all_goals first
      | exact read1_write _ _ _ _ small source
      | exact read2_only _ _ _ _ small source
      | exact (wordStack_inst_cost _ source).trans (by decide)
  | arith operation =>
    cases operation with
    | binop op rd rs operand | shift op rd rs operand =>
      cases operand <;> simp only [WordToStack.Native.wInstNative]
      all_goals first
        | exact read1_write _ _ _ _ small source
        | exact read2_write _ _ _ _ _ small source
    | _ =>
      simp only [WordToStack.Native.wInstNative]
      first
        | exact read2_write _ _ _ _ _ small source
        | exact read1_only _ _ _ small source
        | exact (wordStack_inst_cost _ source).trans (by decide)

#print axioms wordStack_inst_cost
#print axioms wordStack_read_write_cost
#print axioms wordInst_cost
end InitECandidate.Runtime.StackToLab
