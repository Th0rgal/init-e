import InitECandidate.Runtime.WordStackReturningPreludeBound
import InitECandidate.Runtime.WordStackCallDestCost
import InitECandidate.Runtime.WordStackCallSetupCost
import InitECandidate.Runtime.StackCostSeqAssoc
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

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
    (callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (.seq .skip (copyRetNative false false (k,f,frame) values returnCode),0,l1,l2)) destination none)
      {moved with clock := moved.clock + extra} ≤ budget) :
    stackExecutionCost (fun p _ => price p) compiled
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
      stackExecutionCost (fun p _ => price p) prelude s ≤
        26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k :=
    fun s => returningPrelude_cost k f frame names dest args bs savedBitmaps n savedIndex
      destinationCode savedCode destination destinationCompile savedCompile frameSmall argsSmall s
  have preludeShift := Compiler.Backend.StackProps.evaluateAddClock (extra)
    prelude source none moved ⟨completePrelude, by simp⟩
  have reached := stackCost_seq_run (price := price) prelude (.seq .skip callCode)
    {source with clock := source.clock + (extra)}
    {moved with clock := moved.clock + (extra)}
    (26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k)
    preludeShift (prefixBound _)
  have reassoc : stackExecutionCost (fun p _ => price p)
      compiled {source with clock := source.clock + (extra)} =
      stackExecutionCost (fun p _ => price p)
        (.seq prelude (.seq .skip callCode)) {source with clock := source.clock + (extra)} := by
    rw [compiledEq]
    dsimp only [prelude]
    rw [stackCost_seq_assoc]
    exact stackCost_seq_congr_right (price := price) destinationCode _ _
      (fun st => (stackCost_seq_assoc savedCode argsCode (.seq .skip callCode) st).symm) _
  rw [reassoc]
  have skipCall : stackExecutionCost (fun p _ => price p)
      (.seq .skip callCode) {moved with clock := moved.clock + (extra)} =
      stackExecutionCost (fun p _ => price p)
      callCode {moved with clock := moved.clock + (extra)} := by
    rw [stackExecutionCost_seq]
    simp only [show price (.seq .skip callCode) = 0 from ConservativeRemovalPrice.freeSeq _ _,
      stackExecutionCost, show price .skip = 0 from ConservativeRemovalPrice.skip,
      StackSemEvaluate.evaluate_skip, Nat.zero_add]
  rw [skipCall] at reached
  change stackExecutionCost _ (.seq prelude (.seq .skip callCode)) _ ≤ _
  change stackExecutionCost _ callCode _ ≤ _ at callCost
  omega

#print axioms compiledCall_cost_from_prelude
end InitECandidate.Runtime.WordToStack.ExecutedReturning
