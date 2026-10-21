import InitECandidate.Runtime.WordStackRefinedInstructionPrice

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab

/-- Only registers outside the allocated register window require a spill.
The frame size affects offsets, not the number of emitted loads/stores. -/
def spillCount (k register : Nat) : Nat := if register / 2 < k then 0 else 1

def spillAwareInstructionPrice (k : Nat) : HolInst 64 → Nat
  | .const dst _ => 6 + 6 * spillCount k dst
  | .arith (.binop _ dst src (.imm _)) => 6 + 6 * (spillCount k src + spillCount k dst)
  | .arith (.binop _ dst src (.reg src2)) =>
      6 + 6 * (spillCount k src + spillCount k src2 + spillCount k dst)
  | instruction => refinedNativeInstructionPrice instruction

theorem wReg1_spill_count (register : Nat) (kf : Nat × Nat × Nat) :
    (WordToStackRegFormat.wReg1 register kf).1.length = spillCount kf.1 register := by
  unfold WordToStackRegFormat.wReg1 spillCount
  dsimp only
  split <;> rfl

theorem wReg2_spill_count (register : Nat) (kf : Nat × Nat × Nat) :
    (WordToStackRegFormat.wReg2 register kf).1.length = spillCount kf.1 register := by
  unfold WordToStackRegFormat.wReg2 spillCount
  dsimp only
  split <;> rfl

/-- Keep actual spill-list length instead of replacing it by a worst-case
number of operands. The core budget is proved independently of register names. -/
theorem wordStack_actual_spill_cost {F : Type} (loads : List (Nat × Nat))
    (dst : Nat) (kf : Nat × Nat × Nat) (g : Nat → HolInst 64) (core : Nat)
    (small : kf.2.1 ≤ 92) (loadsSmall : ∀ entry ∈ loads, entry.2 ≤ 91)
    (coreBound : ∀ r, refinedNativePriceWithGap 6 (.inst (g r)) ≤ core)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative loads (wRegWrite1Native (fun r => .inst (g r)) dst kf)) source ≤
      core + 6 * (loads.length + spillCount kf.1 dst) := by
  have bound := wordStack_read_write_refined_cost loads (fun r => .inst (g r)) dst kf core small loadsSmall
    (fun r s => by simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap] using coreBound r) source
  unfold spillCount
  split_ifs at bound ⊢ <;> omega

/-- Sound spill-sensitive prices for literal constants and binary operators.
Other instructions retain the existing proved conservative price. The native
encoding gap is still six here; no unproved reduction of padding is used. -/
theorem wordStack_spill_aware_instruction_cost {F : Type} (instruction : HolInst 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wInstNative instruction kf) source ≤ spillAwareInstructionPrice kf.1 instruction := by
  cases instruction with
  | skip | mem _ _ _ => exact wordStack_refined_native_instruction_cost _ kf small source
  | const dst value =>
    have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
        stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
          (.inst (.const r value)) s ≤ 6 := by
      intro r s
      have bound := const_native_length_le r value
      simpa only [stackExecutionCost, refinedRemovalLocalPrice, refinedNativePriceWithGap,
        instLocalCost, max_le_iff, Nat.le_refl, and_true] using bound
    have bound := wordRegWrite1_refined_cost (fun r => .inst (.const r value)) dst kf 6 small core source
    simp only [wInstNative, spillAwareInstructionPrice]
    unfold spillCount
    split_ifs at bound ⊢ <;> omega
  | arith operation =>
    cases operation with
    | binop op dst src operand =>
      have loads1 := wordReg1_loads src kf small
      cases operand with
      | imm value =>
        simp only [wInstNative, spillAwareInstructionPrice]
        have bound := wordStack_actual_spill_cost (WordToStackRegFormat.wReg1 src kf).1 dst kf
          (fun r => .arith (.binop op r (WordToStackRegFormat.wReg1 src kf).2 (.imm value))) 6
          small loads1.2 (fun r => by simp [refinedNativePriceWithGap, instLocalCost]) source
        simpa only [wReg1_spill_count] using bound
      | reg src2 =>
        have loads2 := wordReg2_loads src2 kf small
        have checked : ∀ entry ∈
            (WordToStackRegFormat.wReg1 src kf).1 ++ (WordToStackRegFormat.wReg2 src2 kf).1,
            entry.2 ≤ 91 := by
          intro entry member
          rcases List.mem_append.mp member with member | member
          · exact loads1.2 entry member
          · exact loads2.2 entry member
        simp only [wInstNative, spillAwareInstructionPrice]
        have bound := wordStack_actual_spill_cost _ dst kf
          (fun r => .arith (.binop op r (WordToStackRegFormat.wReg1 src kf).2
            (.reg (WordToStackRegFormat.wReg2 src2 kf).2))) 6 small checked
          (fun r => by simp [refinedNativePriceWithGap, instLocalCost]) source
        simpa only [List.length_append, wReg1_spill_count, wReg2_spill_count] using bound
    | _ => exact wordStack_refined_native_instruction_cost _ kf small source

/-- A binary operation whose operands and result are all in registers pays
six under the existing gap-six envelope, rather than the worst-spill price24. -/
theorem register_binop_price (k dst src src2 : Nat) (op : BinOp)
    (hd : dst / 2 < k) (hs : src / 2 < k) (hs2 : src2 / 2 < k) :
    spillAwareInstructionPrice k (.arith (.binop op dst src (.reg src2))) = 6 := by
  simp [spillAwareInstructionPrice, spillCount, hd, hs, hs2]

#print axioms wReg1_spill_count
#print axioms wReg2_spill_count
#print axioms wordStack_actual_spill_cost
#print axioms wordStack_spill_aware_instruction_cost
#print axioms register_binop_price
end InitECandidate.Runtime.WordToStack
