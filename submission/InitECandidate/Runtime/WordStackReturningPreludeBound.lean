import InitECandidate.Runtime.WordStackCallDestCost
import InitECandidate.Runtime.WordStackCallSetupCost
import InitECandidate.Runtime.StackCostSeqAssoc
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- The actual destination/save/argument fragment has a uniform local cost,
independent of whether argument-frame allocation succeeds. -/
theorem returningPrelude_cost {F : Type}
    (k f frame : Nat) (names : WordLangCutsetsHOL) (dest : Option Nat) (args : List Nat)
    (bs savedBitmaps : AppList (BitVec 64)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg 64) (destination : Sum Nat Nat)
    (destinationCompile : callDestNative dest args (k,f,frame) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,f,frame) = (savedCode,(savedBitmaps,savedIndex)))
    (frameSmall : f ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p)
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame)))) s ≤
      26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by

  have destinationBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) destinationCode st ≤ 7 := by
    intro st
    have eq : (callDestNative dest args (k,f,frame)).1 = destinationCode := congrArg Prod.fst destinationCompile
    rw [← eq]
    exact (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_callDest_cost dest args _ frameSmall st)
  have saveBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) savedCode st ≤ 19 := by
    intro st
    have eq : (wLiveNative names (bs,n) (k,f,frame)).1 = savedCode := congrArg Prod.fst savedCompile
    rw [← eq]
    exact (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_live_cost names (bs,n) (k,f,frame) st)
  have argumentsBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) (stackArgsNative destination (args.length+1) (k,f,frame)) st ≤
        39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
    intro st
    exact (ConservativeRemovalPrice.execution (price := price) (stackArgsNative destination (args.length+1) (k,f,frame)) st).trans
      (wordStack_stackArgs_cost destination (args.length+1) (k,f,frame) frameSmall argsSmall st)
  have savedArgs : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))) st ≤
      19 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
    intro st
    exact stackCost_seq_le (price) savedCode (stackArgsNative destination (args.length+1) (k,f,frame))
      19 _ (ConservativeRemovalPrice.freeSeq _ _) saveBound argumentsBound st
  have bound := stackCost_seq_le (price) destinationCode
    (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))) 7 _ (ConservativeRemovalPrice.freeSeq _ _) destinationBound savedArgs s
  change stackExecutionCost _ (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame)))) s ≤ _ at bound
  omega

#print axioms returningPrelude_cost
end InitECandidate.Runtime.WordToStack.ExecutedReturning
