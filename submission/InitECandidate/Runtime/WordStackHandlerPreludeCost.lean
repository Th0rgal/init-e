import InitECandidate.Runtime.WordStackReturningPreludeBound
import InitECandidate.Runtime.WordStackHandlerRestoreCost
namespace InitECandidate.Runtime.WordToStack.ExecutedHandler
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Destination, saved frame, three-word handler header and argument movement
are priced by their actual generated fragments, including early stops. -/
theorem handlerPrelude_cost {F : Type}
    (k frame payload h1 h2 : Nat) (names : WordLangCutsetsHOL) (dest : Option Nat) (args : List Nat)
    (bs savedBs : AppList (BitVec 64)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg 64) (destination : Sum Nat Nat)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (frameSmall : frame ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p)
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload))))) s ≤
      131 + 39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by
  have destinationBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) destinationCode st ≤ 7 := by
    intro st
    have eq := congrArg Prod.fst destinationCompile
    dsimp only at eq
    rw [← eq]
    exact (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_callDest_cost dest args _ frameSmall st)
  have saveBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) savedCode st ≤ 19 := by
    intro st
    have eq := congrArg Prod.fst savedCompile
    dsimp only at eq
    rw [← eq]
    exact (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_live_cost names (bs,n) (k,frame,payload) st)
  have pushBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) (pushHandlerNative false h1 h2 (k,frame,payload)) st ≤ 105 :=
    fun st => (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_pushHandler_cost h1 h2 (k,frame,payload) st)
  have argsBound : ∀ st : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p)
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)) st ≤
        39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k :=
    fun st => (ConservativeRemovalPrice.execution (price := price) _ st).trans
      (wordStack_stackHandlerArgs_cost destination (args.length+1) (k,frame,payload) frameSmall argsSmall st)
  have pushedArgs := fun st => stackCost_seq_le price _ _ 105 _
    (ConservativeRemovalPrice.freeSeq _ _) pushBound argsBound st
  have savedPushArgs := fun st => stackCost_seq_le price _ _ 19 _
    (ConservativeRemovalPrice.freeSeq _ _) saveBound pushedArgs st
  have bound := stackCost_seq_le price _ _ 7 _
    (ConservativeRemovalPrice.freeSeq _ _) destinationBound savedPushArgs s
  exact bound.trans (by omega)

theorem compiledHandlerCall_cost_from_prelude {F : Type}
    (ac : AsmConfigExact 64) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec 64))
    (l1 l2 handlerVar h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBs retBs handlerBs : AppList (BitVec 64))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg 64)
    (destination : Sum Nat Nat)
    (target moved targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (extra : Nat) (result : Option (StackSemResult 64))
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
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (none,moved))
    (frameSmall : frame ≤ 92)
    (argsSmall : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤ 92)
    (budget : Nat)
    (callCost : stackExecutionCost (fun p _ => price p)
      (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode)),0,l1,l2))
        destination (some (handlerTarget,h1,h2))) {moved with clock := moved.clock+extra} ≤ budget) :
    stackExecutionCost (fun p _ => price p) compiled {target with clock := target.clock+extra} ≤
      131 + 39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k + budget := by
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
  have reassoc : stackExecutionCost (fun p _ => price p) compiled {target with clock := target.clock+extra} =
      stackExecutionCost (fun p _ => price p) (.seq prelude (.seq .skip callCode)) {target with clock := target.clock+extra} := by
    rw [compiledEq]
    dsimp only [prelude]
    rw [stackCost_seq_assoc]
    apply stackCost_seq_congr_right (price := price)
    intro afterDestination
    rw [stackCost_seq_assoc]
    apply stackCost_seq_congr_right (price := price)
    intro afterSave
    exact (stackCost_seq_assoc (price := price) pushCode argsCode (.seq .skip callCode) afterSave).symm
  have shifted := Compiler.Backend.StackProps.evaluateAddClock extra prelude target none moved ⟨preludeRun,by simp⟩
  have prefixCost := handlerPrelude_cost (price := price) k frame payload h1 h2 names dest args bs savedBs
    n savedIndex destinationCode savedCode destination destinationCompile savedCompile frameSmall argsSmall
    {target with clock := target.clock+extra}
  have bound := stackCost_seq_run (price := price) prelude (.seq .skip callCode)
    {target with clock := target.clock+extra} {moved with clock := moved.clock+extra}
    (131+39*Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k) shifted prefixCost
  rw [reassoc]
  rw [stackCost_seq_skip_left (price := price)] at bound
  exact bound.trans (Nat.add_le_add_left callCost _)

#print axioms handlerPrelude_cost
#print axioms compiledHandlerCall_cost_from_prelude
end InitECandidate.Runtime.WordToStack.ExecutedHandler
