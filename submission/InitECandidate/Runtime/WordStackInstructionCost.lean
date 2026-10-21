import InitECandidate.Runtime.WordStackSpillCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

theorem wordReg1_loads (register : Nat) (kf : Nat × Nat × Nat)
    (small : kf.2.1 ≤ 92) :
    (WordToStackRegFormat.wReg1 register kf).1.length ≤ 1 ∧
      ∀ entry ∈ (WordToStackRegFormat.wReg1 register kf).1, entry.2 ≤ 91 := by
  by_cases h : register / 2 < kf.1
  · simp [WordToStackRegFormat.wReg1, h]
  · simp [WordToStackRegFormat.wReg1, h]
    omega

theorem wordReg2_loads (register : Nat) (kf : Nat × Nat × Nat)
    (small : kf.2.1 ≤ 92) :
    (WordToStackRegFormat.wReg2 register kf).1.length ≤ 1 ∧
      ∀ entry ∈ (WordToStackRegFormat.wReg2 register kf).1, entry.2 ≤ 91 := by
  by_cases h : register / 2 < kf.1
  · simp [WordToStackRegFormat.wReg2, h]
  · simp [WordToStackRegFormat.wReg2, h]
    omega

/-- A literal register binary operation takes at most two spill loads,
one instruction and one spill store: 28 native steps with the concrete
encoder gap. This counts only this executed instruction's fragment. -/
theorem wordInst_binop_reg_cost {F : Type} (op : BinOp) (dst left right : Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wInstNative (.arith (.binop op dst left (.reg right))) kf) source ≤ 28 := by
  have load1 := wordReg1_loads left kf small
  have load2 := wordReg2_loads right kf small
  let l := WordToStackRegFormat.wReg1 left kf
  let r := WordToStackRegFormat.wReg2 right kf
  have loadsSmall : ∀ entry ∈ l.1 ++ r.1, entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact load1.2 entry member
    · exact load2.2 entry member
  have coreBound : ∀ (n : Nat) (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.inst (.arith (.binop op n l.2 (.reg r.2)))) s ≤ 7 := by
    intro n s
    simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
  have writeBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (WordToStack.Native.wRegWrite1Native
          (fun n => .inst (.arith (.binop op n l.2 (.reg r.2)))) dst kf) s ≤ 14 := by
    intro s
    have bound := wordRegWrite1_cost _ dst kf 7 small coreBound s
    split_ifs at bound <;> omega
  have bound := wordStackLoad_cost (l.1 ++ r.1) _ 14 loadsSmall writeBound source
  have lengthBound : (l.1 ++ r.1).length ≤ 2 := by
    rw [List.length_append]
    exact (Nat.add_le_add load1.1 load2.1)
  change stackExecutionCost _
    (WordToStack.Native.wStackLoadNative (l.1 ++ r.1)
      (WordToStack.Native.wRegWrite1Native
        (fun n => .inst (.arith (.binop op n l.2 (.reg r.2)))) dst kf)) source ≤ 28
  omega

#print axioms wordReg1_loads
#print axioms wordReg2_loads
#print axioms wordInst_binop_reg_cost
end InitECandidate.Runtime.StackToLab
