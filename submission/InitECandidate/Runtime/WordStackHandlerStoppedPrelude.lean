import InitECandidate.Runtime.WordStackHandlerPreludeCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Header/argument allocation failure removes the unexecuted native call
and both continuations from the whole compiled execution cost. -/
theorem compiledHandlerCall_cost_stopped_prelude {F : Type}
    (ac : AsmConfigExact 64) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec 64))
    (l1 l2 handlerVar h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBs retBs handlerBs : AppList (BitVec 64))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg 64)
    (destination : Sum Nat Nat)
    (target stoppedPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (stopped : StackSemResult 64)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (stoppedPrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (some stopped,stoppedPost))
    (frameSmall : frame ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92) :
    stackExecutionCost (fun p _ => price p) compiled target ≤
      131+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  let argsCode : HolProg 64 := stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)
  let pushCode : HolProg 64 := pushHandlerNative false h1 h2 (k,frame,payload)
  let returnSuffix : HolProg 64 := .seq .skip (copyRetNative false true (k,frame,payload) values
    (popHandlerNative false (k,frame,payload) returnCode))
  let callCode : HolProg 64 := .call (some (returnSuffix,0,l1,l2)) destination (some (handlerTarget,h1,h2))
  let prelude : HolProg 64 := .seq destinationCode (.seq savedCode (.seq pushCode argsCode))
  have compiledEq : compiled = .seq destinationCode (.seq savedCode (.seq pushCode (.seq argsCode (.seq .skip callCode)))) := by
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile] at shape
    simpa only [Bool.false_eq_true,↓reduceIte] using (Prod.mk.inj shape).1.symm
  have reassoc : stackExecutionCost (fun p _ => price p) compiled target =
      stackExecutionCost (fun p _ => price p) (.seq prelude (.seq .skip callCode)) target := by
    rw [compiledEq]
    exact stackCost_seq_four_factor (price := price) destinationCode savedCode pushCode argsCode
      (.seq .skip callCode) _
  change StackSemEvaluate.evaluate (prelude,target) = (some stopped,stoppedPost) at stoppedPrelude
  rw [reassoc,stackExecutionCost_seq]
  simp only [ConservativeRemovalPrice.freeSeq (price := price),Nat.zero_add,stoppedPrelude,Nat.add_zero]
  exact handlerPrelude_cost (price := price) k frame payload h1 h2 names dest args bs savedBs n savedIndex
    destinationCode savedCode destination destinationCompile savedCompile frameSmall argsSmall target

#print axioms compiledHandlerCall_cost_stopped_prelude
end InitECandidate.Runtime.WordToStack.ExecutedHandler
