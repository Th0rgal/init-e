import InitECandidate.Runtime.WordStackHandlerGuarded
import InitECandidate.Runtime.WordStackReturningCounts
import InitECandidate.Runtime.WordStackHandlerSuccessful
import InitECandidate.Runtime.WordStackHandlerHeaderFailureCost
import InitECandidate.Runtime.WordStackHandlerArgumentsFailureCost
import InitECandidate.Runtime.WordStackHandlerTimeoutCost
import InitECandidate.Runtime.WordStackHandlerCalleeFailureCost
import InitECandidate.Runtime.WordStackHandlerCallee
import InitECandidate.Runtime.WordStackHandlerNormalHistory
import InitECandidate.Runtime.WordStackHandlerExceptionHistory
import InitECandidate.Runtime.StackReturningCallPropagateCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]



/-- Complete returning handler constructor with the original simulation premises. -/
theorem executedSimulation_returningHandler (calleeBudget returnBudget handlerBudget : Nat) {F : Type}
    (ac : AsmConfigExact 64) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (covered : CodeFramesBounded source.code source.stackSize 92)
    (ih : InductionHypotheses price calleeBudget returnBudget handlerBudget ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source) :
    ExecutedSimulationFor price ac (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source
      (calleeBudget + returnBudget + handlerBudget + 189 + 39*(args.length+1-22) + 21*(values.length+1-22)) := by
  apply executedSimulationFor_of_registers price
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises frameSmall actualRegisters
  obtain ⟨execution, notError, related, conventions, flat, compilation, bitmapLength,
    bitmapBound, bitmapPrefix, labels, maximum⟩ := premises
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotErrorWithHandler values names retCode l1 l2
    dest args (some (handlerVar,handlerCode,h1,h2)) source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := 64) dest args (k, f, frame) with ⟨destinationCode, destination⟩
  rcases savedCompile : wLiveNative names (bs, n) (k, f, frame) with
    ⟨savedCode, savedBitmaps, savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) with
    ⟨returnCode, returnBitmaps, returnIndex⟩
  rcases handlerCompile : compNative ac false handlerCode (returnBitmaps,returnIndex) (k,f,frame) with
    ⟨handlerTarget,handlerBitmaps,handlerIndex⟩
  have shape := compilation
  simp only [compNative, destinationCompile, savedCompile, returnCompile, handlerCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at shape
  obtain ⟨bitmapsEq, indexEq⟩ := shape.2
  subst finalBitmaps
  subst finalIndex
  have noHandlerConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  have noHandlerMaximum := lt_of_le_of_lt (maximumWithoutHandler values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2))) maximum
  have argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92 :=
    (CallReturning.stackArgumentFrameBound ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs destinationCode destination guards related noHandlerConventions noHandlerMaximum destinationCompile).trans frameSmall
  have returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92 :=
    (ExecutedReturning.returningReturnCount_le_frame ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs guards related noHandlerConventions noHandlerMaximum).trans frameSmall
  have argsUpper : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ args.length+1-22 := by
    rw [actualRegisters]
    cases destination <;> simp only [Compiler.Backend.WordToStack.stackArgCount] <;> omega
  have returnsEq : Compiler.Backend.WordToStack.numStackRet k values = values.length+1-22 := by
    rw [actualRegisters]
    rfl
  obtain ⟨extra,post,out,run,contract,cost⟩ :=
    InitECandidate.Runtime.WordToStack.ExecutedHandler.simulateHandlerCallWithGuards (price := price)
      calleeBudget returnBudget handlerBudget ac k f frame values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source sourcePost result target lens xs args1 prog ss envs bs
      savedBitmaps returnBitmaps handlerBitmaps n savedIndex returnIndex handlerIndex destinationCode
      savedCode returnCode handlerTarget compiled destination guards related conventions flat maximum
      destinationCompile savedCompile returnCompile handlerCompile compilation bitmapLength bitmapBound
      bitmapPrefix labels execution notError covered frameSmall argsSmall returnsSmall actualRegisters ih
  refine ⟨extra,post,out,run,contract,?_⟩
  omega

#print axioms executedSimulation_returningHandler
end InitECandidate.Runtime.WordToStack.ExecutedHandler
