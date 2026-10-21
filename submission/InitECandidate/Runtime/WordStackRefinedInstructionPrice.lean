import InitECandidate.Runtime.WordStackRefinedSpillCost
import InitECandidate.Runtime.WordStackInstructionCost
import InitECandidate.Runtime.InstBudget
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab

/-- Native prices distinguish ordinary operations from the generic maximum.
The register indices do not affect these worst-case spill counts. -/
def refinedNativeInstructionPrice : HolInst 64 → Nat
  | .skip => 6
  | .const _ _ => 12
  | .arith (.binop _ _ _ (.imm _)) => 18
  | .arith (.binop _ _ _ (.reg _)) => 24
  | .arith (.shift _ _ _ (.imm _)) => 22
  | .arith (.shift _ _ _ (.reg _)) => 28
  | .arith (.div _ _ _) => 24
  | .arith (.longMul _ _ _ _) => 21
  | .arith (.longDiv _ _ _ _ _) => 27
  | .arith _ => 39
  | .mem _ _ _ => 18

theorem refinedNativeInstructionPrice_le (instruction : HolInst 64) :
    refinedNativeInstructionPrice instruction ≤ 39 := by
  cases instruction with
  | skip | const _ _ | mem _ _ _ => simp [refinedNativeInstructionPrice]
  | arith operation =>
    cases operation with
    | binop _ _ _ operand | shift _ _ _ operand => cases operand <;> simp [refinedNativeInstructionPrice]
    | _ => simp [refinedNativeInstructionPrice]

theorem wordStack_read_write_refined_cost {F : Type} (loads : List (Nat × Nat))
    (g : Nat → HolProg 64) (dst : Nat) (kf : Nat × Nat × Nat) (budget : Nat)
    (small : kf.2.1 ≤ 92) (loadsSmall : ∀ entry ∈ loads, entry.2 ≤ 91)
    (core : ∀ n (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p) (g n) s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative loads (wRegWrite1Native g dst kf)) source ≤
      6 * loads.length + budget + (if dst / 2 < kf.1 then 0 else 6) := by
  have bound := wordStackLoad_refined_cost loads _
    (budget + (if dst / 2 < kf.1 then 0 else 6)) loadsSmall
    (fun s => wordRegWrite1_refined_cost g dst kf budget small core s) source
  simpa only [Nat.add_assoc] using bound

theorem wordStack_refined_const_cost {F : Type} (dst : Nat) (value : BitVec 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wInstNative (.const dst value) kf) source ≤ 12 := by
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.inst (.const r value)) s ≤ 6 := by
    intro r s
    have bound := const_native_length_le r value
    simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost, max_le_iff, Nat.le_refl, and_true] using bound
  have bound := wordRegWrite1_refined_cost (fun r => .inst (.const r value)) dst kf 6 small core source
  simp only [wInstNative]
  split_ifs at bound <;> omega

private theorem oneReadWrite {F : Type} (read dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : ∀ r, refinedNativePriceWithGap 6 (.inst (g r)) ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1
        (wRegWrite1Native (fun r => .inst (g r)) dst kf)) source ≤ 12+core := by
  have loads := wordReg1_loads read kf small
  have bound := wordStack_read_write_refined_cost (WordToStackRegFormat.wReg1 read kf).1 (fun r => .inst (g r)) dst kf core small loads.2
    (fun r s => by simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap] using coreBound r) source
  split_ifs at bound <;> omega

private theorem twoReadWrite {F : Type} (read1 read2 dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : ∀ r, refinedNativePriceWithGap 6 (.inst (g r)) ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (wRegWrite1Native (fun r => .inst (g r)) dst kf)) source ≤ 18+core := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have checked : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStack_read_write_refined_cost _ (fun r => .inst (g r)) dst kf core small checked
    (fun r s => by simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap] using coreBound r) source
  simp only [List.length_append] at bound
  split_ifs at bound <;> omega

private theorem twoRead {F : Type} (read1 read2 : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : refinedNativePriceWithGap 6 (.inst instruction) ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (.inst instruction)) source ≤ 12+core := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have checked : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStackLoad_refined_cost _ (.inst instruction) core checked
    (fun s => by simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap] using coreBound) source
  simp only [List.length_append] at bound
  omega

private theorem oneRead {F : Type} (read : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : refinedNativePriceWithGap 6 (.inst instruction) ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1 (.inst instruction)) source ≤ 6+core := by
  have loads := wordReg1_loads read kf small
  have bound := wordStackLoad_refined_cost _ (.inst instruction) core loads.2
    (fun s => by simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap] using coreBound) source
  omega

theorem wordStack_refined_native_instruction_cost {F : Type} (instruction : HolInst 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wInstNative instruction kf) source ≤ refinedNativeInstructionPrice instruction := by
  cases instruction with
  | skip => simp [wInstNative, stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost, refinedNativeInstructionPrice]
  | const dst value => exact wordStack_refined_const_cost dst value kf small source
  | mem operation dst address =>
    cases address
    cases operation <;> simp only [wInstNative, refinedNativeInstructionPrice]
    all_goals first
      | exact oneReadWrite _ _ _ _ 6 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
      | exact twoRead _ _ _ _ 6 small (by simp [refinedNativePriceWithGap, instLocalCost]) source
      | simp [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost]
  | arith operation =>
    cases operation with
    | binop op dst src operand =>
      cases operand <;> simp only [wInstNative, refinedNativeInstructionPrice]
      all_goals first
        | exact oneReadWrite _ _ _ _ 6 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
        | exact twoReadWrite _ _ _ _ _ 6 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
    | shift op dst src operand =>
      cases operand <;> simp only [wInstNative, refinedNativeInstructionPrice]
      all_goals first
        | exact oneReadWrite _ _ _ _ 10 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
        | exact twoReadWrite _ _ _ _ _ 10 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
    | div dst left right =>
      exact twoReadWrite _ _ _ _ _ 6 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
    | longMul a b c d =>
      simp [wInstNative, stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost, refinedNativeInstructionPrice]
    | longDiv a b c d e =>
      exact oneRead _ _ _ 21 small (by simp [refinedNativePriceWithGap, instLocalCost]) source
    | _ =>
      simp only [wInstNative, refinedNativeInstructionPrice]
      first
        | exact twoReadWrite _ _ _ _ _ 21 small (by intro r; simp [refinedNativePriceWithGap, instLocalCost]) source
        | simp [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap, instLocalCost]

#print axioms refinedNativeInstructionPrice_le
#print axioms wordStack_refined_const_cost
#print axioms wordStack_refined_native_instruction_cost
end InitECandidate.Runtime.WordToStack
