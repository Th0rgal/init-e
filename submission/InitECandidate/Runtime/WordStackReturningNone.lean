import InitECandidate.Runtime.WordStackReturningSuccessful
import InitECandidate.Runtime.WordStackReturningArgumentFailure
import InitECandidate.Runtime.WordStackReturningCalleeFailureCost
import InitECandidate.Runtime.WordStackReturningTimeoutCost
import InitECandidate.Runtime.WordStackReturningCounts
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Complete no-handler returning-call simulation. All original source and
resource branches are retained; quantitative register specialization is22. -/
theorem executedSimulation_returningNone (calleeBudget returnBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (ih : InductionHypothesesFor price calleeBudget returnBudget ac values names retCode l1 l2 dest args source) :
    ExecutedSimulationFor price ac (.call (some (values,names,retCode,l1,l2)) dest args none) source
      (calleeBudget + returnBudget + 63 + 39*(args.length+1-22) + 21*(values.length+1-22)) := by
  apply executedSimulationFor_of_registers price
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises frameSmall actualRegisters
  obtain ⟨execution, notError, related, conventions, flat, compilation, bitmapLength,
    bitmapBound, bitmapPrefix, labels, maximum⟩ := premises
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotError values names retCode l1 l2
    dest args source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := 64) dest args (k, f, frame) with ⟨destinationCode, destination⟩
  rcases savedCompile : wLiveNative names (bs, n) (k, f, frame) with
    ⟨savedCode, savedBitmaps, savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) with
    ⟨returnCode, returnBitmaps, returnIndex⟩
  have shape := compilation
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at shape
  obtain ⟨bitmapsEq, indexEq⟩ := shape.2
  subst finalBitmaps
  subst finalIndex
  have argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92 :=
    (stackArgumentFrameBound ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs destinationCode destination guards related conventions maximum destinationCompile).trans frameSmall
  have returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92 :=
    (returningReturnCount_le_frame ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs guards related conventions maximum).trans frameSmall
  have argsUpper : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ args.length+1-22 := by
    rw [actualRegisters]
    cases destination <;> simp only [Compiler.Backend.WordToStack.stackArgCount] <;> omega
  have returnsEq : Compiler.Backend.WordToStack.numStackRet k values = values.length+1-22 := by
    rw [actualRegisters]
    rfl
  by_cases argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace
  · by_cases zero : source.clock = 0
    · obtain ⟨targetPost, run, conclusion⟩ := compiledCallTimeout ac k f frame values names retCode
        l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
        returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
        related conventions maximum destinationCompile savedCompile returnCompile bitmapLength
        bitmapBound compiled compilation execution argumentsSpace zero bitmapPrefix
      have cost := compiledCall_timeout_cost (price := price) ac k f frame values names retCode l1 l2 dest args source sourcePost result target lens
        xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex destinationCode savedCode
        returnCode destination guards related conventions maximum destinationCompile savedCompile returnCompile
        bitmapLength bitmapBound compiled compilation execution
        argumentsSpace zero bitmapPrefix frameSmall argsSmall
      refine ⟨0, targetPost, some .timeOut, by simpa only [Nat.add_zero] using run, conclusion, ?_⟩
      simpa only [Nat.add_zero] using cost.trans (by omega)
    · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
          else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace
      · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
          ⟨bodyResult, bodyPost⟩
        obtain ⟨extra, final, output, run, conclusion, cost⟩ := simulateSuccessfulCall (price := price)
          calleeBudget returnBudget ac k f frame values names retCode l1 l2 dest args source target
          lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex
          destinationCode savedCode returnCode compiled destination guards related conventions maximum
          destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound
          bitmapPrefix sourcePost bodyPost result bodyResult ih zero execution notError bodyRun calleeSpace covered frameSmall argsSmall returnsSmall actualRegisters
        refine ⟨extra, final, output, run, conclusion, ?_⟩
        cases bodyResult with
        | none => simp only at cost; omega
        | some value => cases value <;> simp only at cost <;> omega
      · obtain ⟨calleeSize, _, sizeEq, failure⟩ := compiledCalleeFrameFailure ac k f frame values names
          retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
          returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
          related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound
          compiled compilation execution argumentsSpace zero bitmapPrefix
        obtain ⟨targetPost, run, conclusion⟩ := failure (by rw [sizeEq]; omega)
        have cost := compiledCall_callee_allocation_failure_cost (price := price) ac k f frame values names retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled compilation execution argumentsSpace zero bitmapPrefix covered (by omega) frameSmall argsSmall
        refine ⟨0, targetPost, some (.halt (.word (BitVec.ofNat 64 2))), by simpa only [Nat.add_zero] using run, conclusion, ?_⟩
        simpa only [Nat.add_zero] using cost.trans (by omega)
  · obtain ⟨targetPost, run, conclusion⟩ := compiledStackArgumentsFailure ac k f frame values names
      retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
      returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related
      conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled
      compilation execution (by omega) bitmapPrefix
    have cost := compiledCall_insufficient_args_cost (price := price) ac k f frame values names retCode l1 l2 dest args source sourcePost result target lens
        xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex destinationCode savedCode
        returnCode destination guards related conventions maximum destinationCompile savedCompile returnCompile
        bitmapLength bitmapBound compiled compilation execution
      (by omega) bitmapPrefix frameSmall argsSmall
    refine ⟨0, targetPost, some (.halt (.word (BitVec.ofNat 64 2))), by simpa only [Nat.add_zero] using run, conclusion, ?_⟩
    simpa only [Nat.add_zero] using cost.trans (by omega)


#print axioms executedSimulation_returningNone
end InitECandidate.Runtime.WordToStack.ExecutedReturning
