import InitECandidate.Runtime.WordStackRefinedSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.ShareInst
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

private theorem shared_core {F : Type} (op : HolMemop) (reg ad : Nat) (offset : BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (.shMemOp op reg (.addr ad offset)) source ≤ 1 := by
  simp [stackExecutionCost,refinedRemovalLocalPrice,removalLocalPrice,nativePriceWithGap]

private theorem shared_read_write {F : Type} (ad dst : Nat) (op : HolMemop) (offset : BitVec 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative (WordToStackRegFormat.wReg1 ad kf).1
        (wRegWrite1Native (fun r => .shMemOp op r (.addr (WordToStackRegFormat.wReg1 ad kf).2 offset)) dst kf))
      source ≤ 13 := by
  have loads := wordReg1_loads ad kf small
  have bound := wordStack_read_write_refined_cost (WordToStackRegFormat.wReg1 ad kf).1
    (fun r => .shMemOp op r (.addr (WordToStackRegFormat.wReg1 ad kf).2 offset)) dst kf 1 small loads.2
    (fun r s => shared_core op r _ offset s) source
  split_ifs at bound <;> omega

private theorem shared_two_reads {F : Type} (ad src : Nat) (op : HolMemop) (offset : BitVec 64)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wStackLoadNative ((WordToStackRegFormat.wReg1 ad kf).1 ++ (WordToStackRegFormat.wReg2 src kf).1)
        (.shMemOp op (WordToStackRegFormat.wReg2 src kf).2 (.addr (WordToStackRegFormat.wReg1 ad kf).2 offset)))
      source ≤ 13 := by
  have left := wordReg1_loads ad kf small
  have right := wordReg2_loads src kf small
  have slots : ∀ entry ∈ (WordToStackRegFormat.wReg1 ad kf).1 ++ (WordToStackRegFormat.wReg2 src kf).1,
      entry.2 ≤ 91 := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact left.2 entry member
    · exact right.2 entry member
  have bound := wordStackLoad_refined_cost _
    (.shMemOp op (WordToStackRegFormat.wReg2 src kf).2 (.addr (WordToStackRegFormat.wReg1 ad kf).2 offset)) 1 slots
    (fun s => shared_core op (WordToStackRegFormat.wReg2 src kf).2 (WordToStackRegFormat.wReg1 ad kf).2 offset s) source
  simp only [List.length_append] at bound
  omega

/-- All eight shared-memory widths and directions pay one operation and
at most two spill transfers; addresses retain the compiler's exact offset. -/
theorem wordStack_shared_refined_cost {F : Type} (op : HolMemop) (reg : Nat)
    (address : HolAddr 64) (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wShareInstNative op reg address kf) source ≤ 13 := by
  cases address
  cases op <;> simp only [wShareInstNative]
  all_goals first | exact shared_read_write _ _ _ _ kf small source | exact shared_two_reads _ _ _ _ kf small source

/-- Actual shared-memory compiler correctness plus the closed fragment cost. -/
theorem refinedExecutedSimulation_shareInst {F : Type} (ac : AsmConfigExact 64)
    (op : WordMemOp) (reg : Nat) (expression : WordLangExpHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.shareInst op reg expression) source 13 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
    ac (.shareInst op reg expression) source 13 (ShareInst.compCorrectShareInst ac op reg expression source)
  intro k f frame bs n target small
  simp only [compNative]
  cases address : expToAddrHOL expression with
  | none => simp [stackExecutionCost,refinedRemovalLocalPrice,removalLocalPrice,nativePriceWithGap]
  | some address => exact wordStack_shared_refined_cost op reg _ (k,f,frame) small target

#print axioms wordStack_shared_refined_cost
#print axioms refinedExecutedSimulation_shareInst
end InitECandidate.Runtime.WordToStack
