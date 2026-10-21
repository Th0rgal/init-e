import InitECandidate.Runtime.WordStackExecutedLeaf
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Return
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Releasing a small frame costs at most seven, followed by the reached
suffix. The zero-size compiler clause omits the release entirely. -/
theorem wordStack_free_suffix_cost {F : Type} (count : Nat) (body : HolProg 64)
    (budget : Nat) (small : count ≤ 92)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (seqStackFreeNative count body) source ≤ 7 + budget := by
  unfold seqStackFreeNative
  split
  · exact (bodyBound source).trans (Nat.le_add_left budget 7)
  · apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 budget rfl
      (fun s => ?_) bodyBound source
    simp only [stackExecutionCost]
    exact guest_frame_free_price count small

/-- Actual return lowering reads at most one spilled return address,
releases at most one small frame chunk, and executes the return. -/
theorem executedSimulation_return {F : Type} (ac : AsmConfigExact 64)
    (register : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.return register names) source 15 := by
  apply executedSimulation_of_fragment ac (.return register names) source 15
    (Return.compCorrectReturn ac register names source)
  intro k f frame bs n target small
  simp only [compNative]
  have loads := wordReg1_loads register (k,f,frame) small
  have releaseSmall : WordToStack.skipFree k f frame names ≤ 92 := by
    unfold WordToStack.skipFree
    omega
  have core : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (seqStackFreeNative (WordToStack.skipFree k f frame names)
          (.ret (WordToStackRegFormat.wReg1 register (k,f,frame)).2)) s ≤ 8 := by
    intro s
    exact wordStack_free_suffix_cost _ _ 1 releaseSmall
      (fun state => by simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]) s
  have bound := wordStackLoad_cost _ _ 8 loads.2 core target
  omega

#print axioms wordStack_free_suffix_cost
#print axioms executedSimulation_return
end InitECandidate.Runtime.WordToStack
