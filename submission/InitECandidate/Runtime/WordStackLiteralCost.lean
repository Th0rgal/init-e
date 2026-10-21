import InitECandidate.Runtime.WordStackSingletonMove
import InitECandidate.Runtime.InstBudget
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Runtime.StackToLab

/-- A 64-bit literal uses at most six native constant instructions and,
when spilled, one store. It does not need the generic arithmetic cap. -/
theorem wordStack_const_cost {F : Type} (dst : Nat) (value : BitVec 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wInstNative (.const dst value) kf) source ≤ 19 := by
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.inst (.const r value)) s ≤ 12 := by
    intro r s
    have bound := const_native_length_le r value
    simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
      using Nat.add_le_add_right bound 6
  have bound := wordRegWrite1_cost (fun r => .inst (.const r value)) dst kf 12 small core source
  simp only [wInstNative]
  split_ifs at bound <;> omega

theorem executedSimulation_const {F : Type} (ac : AsmConfigExact 64)
    (dst : Nat) (value : BitVec 64)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.inst (.const dst value)) source 19 := by
  apply executedSimulation_of_fragment ac (.inst (.const dst value)) source 19
    (Inst.compCorrectInst ac (.const dst value) source)
  intro k f frame bs n target small
  simp only [compNative, HolInst.ofWordLangInst]
  exact wordStack_const_cost dst value (k,f,frame) small target

#print axioms wordStack_const_cost
#print axioms executedSimulation_const
end InitECandidate.Runtime.WordToStack
