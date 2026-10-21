import InitECandidate.Runtime.WordStackLiteralCost
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab

/-- Native prices distinguish ordinary operations from the generic maximum.
The register indices do not affect these worst-case spill counts. -/
def nativeInstructionPrice : HolInst 64 → Nat
  | .skip => 7
  | .const _ _ => 19
  | .arith (.binop _ _ _ (.imm _)) => 21
  | .arith (.binop _ _ _ (.reg _)) => 28
  | .arith (.shift _ _ _ (.imm _)) => 25
  | .arith (.shift _ _ _ (.reg _)) => 32
  | .arith (.div _ _ _) => 28
  | .arith (.longMul _ _ _ _) => 22
  | .arith (.longDiv _ _ _ _ _) => 29
  | .arith _ => 43
  | .mem _ _ _ => 21

theorem nativeInstructionPrice_le (instruction : HolInst 64) :
    nativeInstructionPrice instruction ≤ 43 := by
  cases instruction with
  | skip | const _ _ | mem _ _ _ => simp [nativeInstructionPrice]
  | arith operation =>
    cases operation with
    | binop _ _ _ operand | shift _ _ _ operand => cases operand <;> simp [nativeInstructionPrice]
    | _ => simp [nativeInstructionPrice]

private theorem oneReadWrite {F : Type} (read dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : ∀ r, instLocalCost (g r)+6 ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1
        (wRegWrite1Native (fun r => .inst (g r)) dst kf)) source ≤ 14+core := by
  have loads := wordReg1_loads read kf small
  have bound := wordStack_read_write_cost (WordToStackRegFormat.wReg1 read kf).1 (fun r => .inst (g r)) dst kf core small loads.2
    (fun r s => by simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap] using coreBound r) source
  split_ifs at bound <;> omega

private theorem twoReadWrite {F : Type} (read1 read2 dst : Nat) (kf : Nat × Nat × Nat)
    (g : Nat → HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : ∀ r, instLocalCost (g r)+6 ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (wRegWrite1Native (fun r => .inst (g r)) dst kf)) source ≤ 21+core := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have checked : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStack_read_write_cost _ (fun r => .inst (g r)) dst kf core small checked
    (fun r s => by simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap] using coreBound r) source
  simp only [List.length_append] at bound
  split_ifs at bound <;> omega

private theorem twoRead {F : Type} (read1 read2 : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : instLocalCost instruction+6 ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative
        ((WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1)
        (.inst instruction)) source ≤ 14+core := by
  have loads1 := wordReg1_loads read1 kf small
  have loads2 := wordReg2_loads read2 kf small
  have checked : ∀ entry ∈
      (WordToStackRegFormat.wReg1 read1 kf).1 ++ (WordToStackRegFormat.wReg2 read2 kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact loads1.2 entry member
    · exact loads2.2 entry member
  have bound := wordStackLoad_cost _ (.inst instruction) core checked
    (fun s => by simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap] using coreBound) source
  simp only [List.length_append] at bound
  omega

private theorem oneRead {F : Type} (read : Nat) (kf : Nat × Nat × Nat)
    (instruction : HolInst 64) (core : Nat) (small : kf.2.1 ≤ 92)
    (coreBound : instLocalCost instruction+6 ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative (WordToStackRegFormat.wReg1 read kf).1 (.inst instruction)) source ≤ 7+core := by
  have loads := wordReg1_loads read kf small
  have bound := wordStackLoad_cost _ (.inst instruction) core loads.2
    (fun s => by simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap] using coreBound) source
  omega

theorem wordStack_native_instruction_cost {F : Type} (instruction : HolInst 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wInstNative instruction kf) source ≤ nativeInstructionPrice instruction := by
  cases instruction with
  | skip => simp [wInstNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost, nativeInstructionPrice]
  | const dst value => exact wordStack_const_cost dst value kf small source
  | mem operation dst address =>
    cases address
    cases operation <;> simp only [wInstNative, nativeInstructionPrice]
    all_goals first
      | exact oneReadWrite _ _ _ _ 7 small (by intro r; simp [instLocalCost]) source
      | exact twoRead _ _ _ _ 7 small (by simp [instLocalCost]) source
      | simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
  | arith operation =>
    cases operation with
    | binop op dst src operand =>
      cases operand <;> simp only [wInstNative, nativeInstructionPrice]
      all_goals first
        | exact oneReadWrite _ _ _ _ 7 small (by intro r; simp [instLocalCost]) source
        | exact twoReadWrite _ _ _ _ _ 7 small (by intro r; simp [instLocalCost]) source
    | shift op dst src operand =>
      cases operand <;> simp only [wInstNative, nativeInstructionPrice]
      all_goals first
        | exact oneReadWrite _ _ _ _ 11 small (by intro r; simp [instLocalCost]) source
        | exact twoReadWrite _ _ _ _ _ 11 small (by intro r; simp [instLocalCost]) source
    | div dst left right =>
      exact twoReadWrite _ _ _ _ _ 7 small (by intro r; simp [instLocalCost]) source
    | longMul a b c d =>
      simp [wInstNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost, nativeInstructionPrice]
    | longDiv a b c d e =>
      exact oneRead _ _ _ 22 small (by simp [instLocalCost]) source
    | _ =>
      simp only [wInstNative, nativeInstructionPrice]
      first
        | exact twoReadWrite _ _ _ _ _ 22 small (by intro r; simp [instLocalCost]) source
        | simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]

theorem executedSimulation_native_instruction {F : Type} (ac : AsmConfigExact 64)
    (instruction : WordLangInst (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.inst instruction) source
      (nativeInstructionPrice (HolInst.ofWordLangInst instruction)) := by
  apply executedSimulation_of_fragment ac (.inst instruction) source _
    (Inst.compCorrectInst ac instruction source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_native_instruction_cost _ (k,f,frame) small target

#print axioms wordStack_native_instruction_cost
#print axioms executedSimulation_native_instruction
#print axioms nativeInstructionPrice_le
end InitECandidate.Runtime.WordToStack
