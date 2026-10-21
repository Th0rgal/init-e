import InitECandidate.Runtime.WordStackReturningPreludeBound
namespace InitECandidate.Runtime.WordToStack.ExecutedReturning
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Argument-frame allocation failure stops before entering the callee.
Only the actual destination/save/argument prelude is priced. -/
theorem compiledCall_cost_stopped_prelude {F : Type} (ac : AsmConfigExact 64)
    (k f frame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBitmaps finalBitmaps : AppList (BitVec 64)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg 64) (destination : Sum Nat Nat)
    (source stoppedPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stopped : StackSemResult 64)
    (destinationCompile : callDestNative dest args (k,f,frame) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,f,frame) = (savedCode,(savedBitmaps,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,f,frame) =
      (returnCode,(finalBitmaps,finalIndex)))
    (compilation : compNative ac false (.call (some (values,names,retCode,l1,l2)) dest args none)
      (bs,n) (k,f,frame) = (compiled,(finalBitmaps,finalIndex)))
    (frameSmall : f ≤ 92)
    (argsSmall : Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (stoppedPrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (stackArgsNative destination (args.length+1) (k,f,frame))), source) =
      (some stopped,stoppedPost)) :
    stackExecutionCost (fun p _ => price p) compiled source ≤
      26 + 39 * Flapjack.Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  let argsCode : HolProg 64 := stackArgsNative destination (args.length+1) (k,f,frame)
  let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false false (k,f,frame) values returnCode)
  let callCode : HolProg 64 := .call (some (returnSuffix,0,l1,l2)) destination none
  let prelude : HolProg 64 := .seq destinationCode (.seq savedCode argsCode)
  have compiledEq : compiled = .seq destinationCode (.seq savedCode (.seq argsCode (.seq .skip callCode))) := by
    have shape := compilation
    simp only [compNative, destinationCompile, savedCompile, returnCompile] at shape
    simpa only [Bool.false_eq_true, ↓reduceIte] using (Prod.mk.inj shape).1.symm
  have reassoc : stackExecutionCost (fun p _ => price p) compiled source =
      stackExecutionCost (fun p _ => price p) (.seq prelude (.seq .skip callCode)) source := by
    rw [compiledEq]
    dsimp only [prelude]
    rw [stackCost_seq_assoc]
    exact stackCost_seq_congr_right (price := price) destinationCode _ _
      (fun st => (stackCost_seq_assoc (price := price) savedCode argsCode (.seq .skip callCode) st).symm) _
  change StackSemEvaluate.evaluate (prelude, source) = (some stopped, stoppedPost) at stoppedPrelude
  rw [reassoc, stackExecutionCost_seq]
  simp only [ConservativeRemovalPrice.freeSeq (price := price), stoppedPrelude, Nat.zero_add, Nat.add_zero]
  exact returningPrelude_cost (price := price) k f frame names dest args bs savedBitmaps n savedIndex
    destinationCode savedCode destination destinationCompile savedCompile frameSmall argsSmall source

#print axioms compiledCall_cost_stopped_prelude
end InitECandidate.Runtime.WordToStack.ExecutedReturning
