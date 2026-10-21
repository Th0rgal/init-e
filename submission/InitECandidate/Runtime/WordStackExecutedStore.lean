import InitECandidate.Runtime.WordStackExecutedLeaf
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Set
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.OpCurrHeap
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.FFI
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

theorem executedSimulation_set {F : Type} (ac : AsmConfigExact 64)
    (name : WordStoreHOL) (expression : WordLangExpHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.set name expression) source 14 := by
  apply executedSimulation_of_fragment ac (.set name expression) source 14
    (Set.compCorrectSet ac name expression source)
  intro k f frame bs n target small
  have core : ∀ (name : StoreName) r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.set name r) s ≤ 7 := by
    intro name r s
    simp [stackExecutionCost, removalLocalPrice]
  cases expression with
  | var register =>
    have loads := wordReg1_loads register (k,f,frame) small
    cases name <;> simp only [compNative]
    all_goals first
      | (refine (wordStackLoad_cost _ _ 7 loads.2 (core _ _) target).trans ?_; omega)
      | simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  | _ => cases name <;> simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]

theorem executedSimulation_opCurrHeap {F : Type} (ac : AsmConfigExact 64)
    (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.opCurrHeap operator dst src) source 21 := by
  apply executedSimulation_of_fragment ac (.opCurrHeap operator dst src) source 21
    (OpCurrHeap.compCorrectOpCurrHeap ac operator dst src source)
  intro k f frame bs n target small
  simp only [compNative]
  have loads := wordReg1_loads src (k,f,frame) small
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.opCurrHeap operator r (WordToStackRegFormat.wReg1 src (k,f,frame)).2) s ≤ 7 := by
    intro r s
    simp [stackExecutionCost, removalLocalPrice]
  have bound := wordStack_read_write_cost _ _ dst (k,f,frame) 7 small loads.2 core target
  split_ifs at bound <;> omega

theorem executedSimulation_ffi {F : Type} (ac : AsmConfigExact 64)
    (index : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.ffi index ptr1 len1 ptr2 len2 names) source 25 := by
  apply executedSimulation_of_fragment ac (.ffi index ptr1 len1 ptr2 len2 names) source 25
    (fun k f frame => FFI.compCorrectFFI ac index ptr1 len1 ptr2 len2 names k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]

#print axioms executedSimulation_set
#print axioms executedSimulation_opCurrHeap
#print axioms executedSimulation_ffi
end InitECandidate.Runtime.WordToStack
