import InitECandidate.Runtime.WordStackCallDestCost
import InitECandidate.Runtime.WordStackCallSetupCost
import InitECandidate.Runtime.StackCostSeqAssoc
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Prelude overhead adds to the suffix cost at its actual reached state. -/
theorem compiledCall_cost_from_prelude {F : Type} (ac : AsmConfigExact 64)
    (k f frame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg 64) (destination : Sum Nat Nat)
    (source moved : StackSemStateFiniteExact 64 LabToTarget.Config F) (extra budget : Nat)
    (destinationCompile : callDestNative dest args (k,f,frame) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,f,frame) = (savedCode,(savedBitmaps,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,f,frame) =
      (returnCode,(finalBitmaps,finalIndex)))
    (compilation : compNative ac false (.call (some (values,names,retCode,l1,l2)) dest args none)
      (bs,n) (k,f,frame) = (compiled,(finalBitmaps,finalIndex)))
    (frameSmall : f ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))), source) = (none,moved))
    (callCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (.call (some (.seq .skip (copyRetNative false false (k,f,frame) values returnCode),0,l1,l2)) destination none)
      {moved with clock := moved.clock + extra} ≤ budget) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) compiled
      {source with clock := source.clock + extra} ≤
      26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k + budget := by
  let argsCode : HolProg 64 := stackArgsNative destination (args.length+1) (k,f,frame)
  let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false false (k,f,frame) values returnCode)
  let callCode : HolProg 64 := .call (some (returnSuffix,0,l1,l2)) destination none
  let prelude : HolProg 64 := .seq destinationCode (.seq savedCode argsCode)
  have compiledEq : compiled = .seq destinationCode (.seq savedCode (.seq argsCode (.seq .skip callCode))) := by
    have shape := compilation
    simp only [compNative, destinationCompile, savedCompile, returnCompile] at shape
    simpa only [Bool.false_eq_true, ↓reduceIte] using (Prod.mk.inj shape).1.symm
  have prefixBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) prelude s ≤
        26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
    intro s
    have destinationBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) destinationCode st ≤ 7 := by
      intro st
      have eq : (callDestNative dest args (k,f,frame)).1 = destinationCode := congrArg Prod.fst destinationCompile
      rw [← eq]
      exact wordStack_callDest_cost dest args _ frameSmall st
    have saveBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) savedCode st ≤ 19 := by
      intro st
      have eq : (wLiveNative names (bs,n) (k,f,frame)).1 = savedCode := congrArg Prod.fst savedCompile
      rw [← eq]
      exact wordStack_live_cost names (bs,n) (k,f,frame) st
    have argumentsBound := wordStack_stackArgs_cost (F := F) destination (args.length+1)
      (k,f,frame) frameSmall argsSmall
    have savedArgs : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.seq savedCode argsCode) st ≤
        19 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
      intro st
      exact stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) savedCode argsCode
        19 _ rfl saveBound argumentsBound st
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) destinationCode
      (.seq savedCode argsCode) 7 _ rfl destinationBound savedArgs s
    change stackExecutionCost _ prelude s ≤ _ at bound
    omega
  have preludeShift := Compiler.Backend.StackProps.evaluateAddClock (extra)
    prelude source none moved ⟨completePrelude, by simp⟩
  have reached := stackCost_seq_run prelude (.seq .skip callCode)
    {source with clock := source.clock + (extra)}
    {moved with clock := moved.clock + (extra)}
    (26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k)
    preludeShift (prefixBound _)
  have reassoc : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      compiled {source with clock := source.clock + (extra)} =
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.seq prelude (.seq .skip callCode)) {source with clock := source.clock + (extra)} := by
    rw [compiledEq]
    dsimp only [prelude]
    rw [stackCost_seq_assoc]
    exact stackCost_seq_congr_right destinationCode _ _
      (fun st => (stackCost_seq_assoc savedCode argsCode (.seq .skip callCode) st).symm) _
  rw [reassoc]
  have skipCall : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (.seq .skip callCode) {moved with clock := moved.clock + (extra)} =
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      callCode {moved with clock := moved.clock + (extra)} := by
    rw [stackExecutionCost_seq]
    simp only [show removalLocalPrice 6 riscvConfig.addrOffset (.seq .skip callCode) = 0 from rfl,
      stackExecutionCost, show removalLocalPrice 6 riscvConfig.addrOffset .skip = 0 from rfl,
      StackSemEvaluate.evaluate_skip, Nat.zero_add]
  rw [skipCall] at reached
  change stackExecutionCost _ (.seq prelude (.seq .skip callCode)) _ ≤ _
  change stackExecutionCost _ callCode _ ≤ _ at callCost
  omega

#print axioms compiledCall_cost_from_prelude
end InitECandidate.Runtime.WordToStack.ExecutedReturning
