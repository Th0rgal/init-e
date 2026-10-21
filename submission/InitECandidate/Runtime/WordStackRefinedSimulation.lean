import InitECandidate.Runtime.WordStackRefinedInstructionPrice
import InitECandidate.Runtime.WordStackRefinedMoveCost
import InitECandidate.Runtime.StackRefinedRemovalMonotone
import InitECandidate.Runtime.WordStackExecutedLeaf
import InitECandidate.Runtime.WordStackExecutedStore
import InitECandidate.Runtime.WordStackExecutedReturn
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Whole execution motive using the padding-exclusive StackRemove table. -/
abbrev RefinedExecutedSimulation {F : Type} (ac : AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (budget : Nat) : Prop :=
  ExecutedSimulationFor (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac program source budget

theorem executedSimulation_to_refined {F : Type} {ac : AsmConfigExact 64}
    {program : WordLangProgHOL (BitVec 64)}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {budget : Nat}
    (simulation : ExecutedSimulation ac program source budget) :
    RefinedExecutedSimulation ac program source budget :=
  simulation.reprice (refinedRemovalLocalPrice_le 6 riscvConfig.addrOffset)

theorem refinedExecutedSimulation_skip {F : Type} (ac : AsmConfigExact 64)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac .skip source 0 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac .skip source 0
    (fun k f frame => compCorrectSkip ac k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]

theorem refinedExecutedSimulation_tick {F : Type} (ac : AsmConfigExact 64)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac .tick source 6 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac .tick source 6
    (fun k f frame => Clock.compCorrectTick ac k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap, instLocalCost]

theorem refinedExecutedSimulation_break {F : Type} (ac : AsmConfigExact 64) (label : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.break label) source 2 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.break label) source 2
    (fun k f frame => compCorrectBreak ac label k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]

theorem refinedExecutedSimulation_continue {F : Type} (ac : AsmConfigExact 64) (label : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.continue label) source 0 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.continue label) source 0
    (fun k f frame => compCorrectContinue ac label k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]

theorem refinedExecutedSimulation_get {F : Type} (ac : AsmConfigExact 64)
    (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.get register name) source 12 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.get register name) source 12
    (Get.compCorrectGet ac register name source)
  intro k f frame bs n target small
  simp only [compNative]
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.get r (storeNameOfWord name)) s ≤ 6 := by
    intro r s
    simp [stackExecutionCost, refinedRemovalLocalPrice]
  have bound := wordRegWrite1_refined_cost _ register (k,f,frame) 6 small core target
  split_ifs at bound <;> omega

theorem refinedExecutedSimulation_locValue {F : Type} (ac : AsmConfigExact 64)
    (register location : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.locValue register location) source 14 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.locValue register location) source 14
    (LocValue.compCorrectLocValue ac register location source)
  intro k f frame bs n target small
  simp only [compNative]
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.locValue r location 0) s ≤ 8 := by
    intro r s
    simp [stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]
  have bound := wordRegWrite1_refined_cost _ register (k,f,frame) 8 small core target
  split_ifs at bound <;> omega

/-- The original Word-to-Stack relation fixes term depth to zero. A
MustTerminate node therefore errors and cannot satisfy the non-error premise. -/
theorem refinedExecutedSimulation_mustTerminate {F : Type} (ac : AsmConfigExact 64)
    (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.mustTerminate body) source 0 := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  have related := premises.2.2.1
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, termDepth, _⟩
  have actual := premises.1
  rw [WordSemStateFiniteExact.evaluate] at actual
  simp only [termDepth, ↓reduceDIte] at actual
  exact False.elim (premises.2.1 (Prod.mk.inj actual).1.symm)

set_option maxHeartbeats 2000000 in
theorem refinedExecutedSimulation_set {F : Type} (ac : AsmConfigExact 64)
    (name : WordStoreHOL) (expression : WordLangExpHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.set name expression) source 12 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.set name expression) source 12
    (Set.compCorrectSet ac name expression source)
  intro k f frame bs n target small
  have core : ∀ (name : StoreName) r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.set name r) s ≤ 6 := by
    intro name r s
    simp [stackExecutionCost, refinedRemovalLocalPrice]
  cases expression with
  | var register =>
    have loads := wordReg1_loads register (k,f,frame) small
    cases name <;> simp only [compNative]
    all_goals first
      | (refine (wordStackLoad_refined_cost _ _ 6 loads.2 (core _ _) target).trans ?_; omega)
      | simp [stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]
  | _ => cases name <;> simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]

theorem refinedExecutedSimulation_opCurrHeap {F : Type} (ac : AsmConfigExact 64)
    (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.opCurrHeap operator dst src) source 18 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.opCurrHeap operator dst src) source 18
    (OpCurrHeap.compCorrectOpCurrHeap ac operator dst src source)
  intro k f frame bs n target small
  simp only [compNative]
  have loads := wordReg1_loads src (k,f,frame) small
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.opCurrHeap operator r (WordToStackRegFormat.wReg1 src (k,f,frame)).2) s ≤ 6 := by
    intro r s
    simp [stackExecutionCost, refinedRemovalLocalPrice]
  have bound := wordStack_read_write_refined_cost _ _ dst (k,f,frame) 6 small loads.2 core target
  split_ifs at bound <;> omega

theorem refinedExecutedSimulation_ffi {F : Type} (ac : AsmConfigExact 64)
    (index : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.ffi index ptr1 len1 ptr2 len2 names) source 25 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) ac (.ffi index ptr1 len1 ptr2 len2 names) source 25
    (fun k f frame => FFI.compCorrectFFI ac index ptr1 len1 ptr2 len2 names k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]

theorem refinedExecutedSimulation_native_instruction {F : Type} (ac : AsmConfigExact 64)
    (instruction : WordLangInst (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.inst instruction) source
      (refinedNativeInstructionPrice (HolInst.ofWordLangInst instruction)) := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
    ac (.inst instruction) source _ (Inst.compCorrectInst ac instruction source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_refined_native_instruction_cost _ (k,f,frame) small target

theorem refinedExecutedSimulation_move {F : Type} (ac : AsmConfigExact 64)
    (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.move priority moves) source (24*moves.length) := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
    ac (.move priority moves) source _ (MoveFull.compCorrectMove ac priority moves source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_move_refined_cost moves (k,f,frame) small target

/-- Actual scheduler length, including physical-register coalescing. -/
theorem refinedExecutedSimulation_scheduled_move {F : Type} (ac : AsmConfigExact 64)
    (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.move priority moves) source
      (12 * (Parmove.parmove (moves.map (fun move => (move.1/2,move.2/2)))).length) := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
    ac (.move priority moves) source _ (MoveFull.compCorrectMove ac priority moves source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_move_scheduled_refined_cost moves (k,f,frame) small target

theorem refinedExecutedSimulation_singleton_move {F : Type}
    (ac : AsmConfigExact 64) (priority dst src : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    RefinedExecutedSimulation ac (.move priority [(dst,src)]) source 12 := by
  apply executedSimulationFor_of_fragment (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
    ac (.move priority [(dst,src)]) source _ (MoveFull.compCorrectMove ac priority [(dst,src)] source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_singleton_move_refined_cost dst src (k,f,frame) small target

#print axioms executedSimulation_to_refined
#print axioms refinedExecutedSimulation_skip
#print axioms refinedExecutedSimulation_tick
#print axioms refinedExecutedSimulation_break
#print axioms refinedExecutedSimulation_continue
#print axioms refinedExecutedSimulation_get
#print axioms refinedExecutedSimulation_locValue
#print axioms refinedExecutedSimulation_mustTerminate
#print axioms refinedExecutedSimulation_set
#print axioms refinedExecutedSimulation_opCurrHeap
#print axioms refinedExecutedSimulation_ffi
#print axioms refinedExecutedSimulation_native_instruction
#print axioms refinedExecutedSimulation_move
#print axioms refinedExecutedSimulation_scheduled_move
#print axioms refinedExecutedSimulation_singleton_move
end InitECandidate.Runtime.WordToStack
