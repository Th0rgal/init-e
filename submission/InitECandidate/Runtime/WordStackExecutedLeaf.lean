import InitECandidate.Runtime.WordStackExecutedSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Clock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Get
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.LocValue
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Attach a proved uniform fragment cost to an original semantic witness.
The concrete leaf theorems below discharge this local compiler-code obligation. -/
theorem executedSimulation_of_fragment {F : Type} (ac : AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (budget : Nat)
    (simulation : Flapjack.WordToStackProofs.CompCorrect.Seq.Simulation ac program source)
    (fragment : ∀ (k f frame : Nat) (bs : AppList (BitVec 64)) (n : Nat)
      (target : StackSemStateFiniteExact 64 LabToTarget.Config F), f ≤ 92 →
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (compNative ac false program (bs,n) (k,f,frame)).1 target ≤ budget) :
    ExecutedSimulation ac program source budget := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  obtain ⟨clock, final, output, run, related⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises
  refine ⟨clock, final, output, run, related, ?_⟩
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  dsimp only at programEq
  rw [← programEq]
  exact fragment k f frame bs n {target with clock := target.clock+clock} small

theorem executedSimulation_skip {F : Type} (ac : AsmConfigExact 64)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac .skip source 0 := by
  apply executedSimulation_of_fragment ac .skip source 0
    (fun k f frame => compCorrectSkip ac k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]

theorem executedSimulation_tick {F : Type} (ac : AsmConfigExact 64)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac .tick source 7 := by
  apply executedSimulation_of_fragment ac .tick source 7
    (fun k f frame => Clock.compCorrectTick ac k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]

theorem executedSimulation_break {F : Type} (ac : AsmConfigExact 64) (label : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.break label) source 2 := by
  apply executedSimulation_of_fragment ac (.break label) source 2
    (fun k f frame => compCorrectBreak ac label k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]

theorem executedSimulation_continue {F : Type} (ac : AsmConfigExact 64) (label : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.continue label) source 0 := by
  apply executedSimulation_of_fragment ac (.continue label) source 0
    (fun k f frame => compCorrectContinue ac label k f frame source)
  intro k f frame bs n target small
  simp [compNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]

theorem executedSimulation_get {F : Type} (ac : AsmConfigExact 64)
    (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.get register name) source 14 := by
  apply executedSimulation_of_fragment ac (.get register name) source 14
    (Get.compCorrectGet ac register name source)
  intro k f frame bs n target small
  simp only [compNative]
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.get r (storeNameOfWord name)) s ≤ 7 := by
    intro r s
    simp [stackExecutionCost, removalLocalPrice]
  have bound := wordRegWrite1_cost _ register (k,f,frame) 7 small core target
  split_ifs at bound <;> omega

theorem executedSimulation_locValue {F : Type} (ac : AsmConfigExact 64)
    (register location : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.locValue register location) source 15 := by
  apply executedSimulation_of_fragment ac (.locValue register location) source 15
    (LocValue.compCorrectLocValue ac register location source)
  intro k f frame bs n target small
  simp only [compNative]
  have core : ∀ r (s : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.locValue r location 0) s ≤ 8 := by
    intro r s
    simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  have bound := wordRegWrite1_cost _ register (k,f,frame) 8 small core target
  split_ifs at bound <;> omega

/-- The original Word-to-Stack relation fixes term depth to zero. A
MustTerminate node therefore errors and cannot satisfy the non-error premise. -/
theorem executedSimulation_mustTerminate {F : Type} (ac : AsmConfigExact 64)
    (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.mustTerminate body) source 0 := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  have related := premises.2.2.1
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, termDepth, _⟩
  have actual := premises.1
  rw [WordSemStateFiniteExact.evaluate] at actual
  simp only [termDepth, ↓reduceDIte] at actual
  exact False.elim (premises.2.1 (Prod.mk.inj actual).1.symm)

#print axioms executedSimulation_skip
#print axioms executedSimulation_tick
#print axioms executedSimulation_break
#print axioms executedSimulation_continue
#print axioms executedSimulation_get
#print axioms executedSimulation_locValue
#print axioms executedSimulation_mustTerminate
end InitECandidate.Runtime.WordToStack
