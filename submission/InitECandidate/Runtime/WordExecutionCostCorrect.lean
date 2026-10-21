import InitECandidate.Runtime.WordExecutionCostCaps
import InitECandidate.Runtime.WordStackFineControlPrice
import InitECandidate.Runtime.WordStackFineTailPrice
import InitECandidate.Runtime.WordStackFineReturningConstructor
import InitECandidate.Runtime.WordStackFineHandlerConstructor
import InitECandidate.Runtime.WordStackRefinedComposition
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.FineCost InitECandidate.Runtime.StackToLab

private theorem fine_leaf_of_isSome {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (caps : FineWordCostCaps price factor)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (supported : (refinedWordStackLeafBudget program).isSome = true) :
    RefinedExecutedSimulation ac program source (factor * wordExecutionCost price program source) := by
  cases priced : refinedWordStackLeafBudget program with
  | none => simp only [priced,Option.isSome_none,Bool.false_eq_true] at supported
  | some budget =>
      exact refinedExecutedSimulation_fine_leaf ac price factor program source budget priced
        (caps.leaf program source budget priced)

/-- Whole executed-cost compiler theorem. Recursion follows only the source
termination measure; target execution witnesses and costs are constructed by
the compiler-fragment proofs. No whole-run target bound is assumed. -/
theorem wordExecutionCost_correct {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (caps : FineWordCostCaps price factor) :
    ∀ (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F),
      wordCostSupported program = true → CostSupportedCode source.code →
      CodeFramesBounded source.code source.stackSize 92 →
      RefinedExecutedSimulation ac program source (factor * wordExecutionCost price program source)
  | .seq first second, source, supported, code, frames => by
      have parts : wordCostSupported first = true ∧ wordCostSupported second = true := by
        simpa only [wordCostSupported,Bool.and_eq_true] using supported
      apply executedSimulation_seqWithPrice _ (fun _ _ => rfl) ac price factor first second source
        (caps.seqFree first second source)
      · exact wordExecutionCost_correct ac price factor caps first source parts.1 code frames
      · intro post run
        have clock := evaluate_clock first source none post run
        exact wordExecutionCost_correct ac price factor caps second post parts.2
          (code.after_evaluate parts.1 run)
          (frames.after_evaluate (wordCostSupported_noInstall first parts.1) code.noInstallCode run)
  | .ite cmp reg operand first second, source, supported, code, frames => by
      have parts : wordCostSupported first = true ∧ wordCostSupported second = true := by
        simpa only [wordCostSupported,Bool.and_eq_true] using supported
      apply executedSimulation_iteWithPrice _ 6 6 11 23 refinedConditionPriceCaps ac price factor
        cmp reg operand first second source (caps.condition cmp reg operand first second source)
      · intro x y left right compared
        exact wordExecutionCost_correct ac price factor caps first source parts.1 code frames
      · intro x y left right compared
        exact wordExecutionCost_correct ac price factor caps second source parts.2 code frames
  | .loop names body exitNames, source, supported, code, frames => by
      have bodySupported : wordCostSupported body = true := supported
      apply executedSimulation_loopWithPrice _ (fun _ => rfl) ac price factor names exitNames body source
        (caps.loop names body exitNames source)
      · intro cutSource cut
        obtain ⟨locals,cutEq⟩ := cutStateConst (names,.ln) source cutSource cut
        have clock := cutState_clock_termdep (names,.ln) source cutSource cut
        exact wordExecutionCost_correct ac price factor caps body cutSource bodySupported
          (by rw [cutEq]; exact code) (frames.after_cutState cut)
      · intro cutSource result post cut run continues nonzero
        obtain ⟨locals,cutEq⟩ := cutStateConst (names,.ln) source cutSource cut
        have clock := evaluate_clock body cutSource result post run
        have cutClock := cutState_clock_termdep (names,.ln) source cutSource cut
        have cutCode : CostSupportedCode cutSource.code := by rw [cutEq]; exact code
        have cutFrames := frames.after_cutState cut
        exact wordExecutionCost_correct ac price factor caps (wordSemSTOP (.loop names body exitNames))
          (WordSemStateFiniteExact.decClock post) supported
          (cutCode.after_evaluate (post := post) bodySupported run)
          (cutFrames.after_evaluate (post := post) (wordCostSupported_noInstall body bodySupported) cutCode.noInstallCode run)
  | .call none dest args handler, source, supported, code, frames => by
      apply executedSimulation_tailCallWithPrice _ ac price factor dest args handler source frames
        (caps.tail dest args handler source)
      intro xs args1 prog ss facts
      rcases facts with ⟨get,bad,find,noHandler,nonzero⟩
      subst handler
      exact wordExecutionCost_correct ac price factor caps prog
        (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))
        (code.findCode dest (wordSemAddRetLoc none xs) args1 prog ss find) code frames
  | .call (some (values,names,retCode,l1,l2)) dest args none, source, supported, code, frames => by
      have retSupported : wordCostSupported retCode = true := by
        simpa only [wordCostSupported,Bool.and_true,Bool.true_and,Bool.and_eq_true] using supported
      apply executedSimulation_returningNone_fine _ price factor ac values names retCode l1 l2 dest args
        source frames (caps.returning values names retCode l1 l2 dest args source)
      · intro xs args1 prog ss envs guards nonzero
        exact wordExecutionCost_correct ac price factor caps prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs none (WordSemStateFiniteExact.decClock source)))
          (code.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) args1 prog ss guards.2.2.1)
          code frames
      · intro xs args1 prog ss envs location returned post popped guards nonzero run valid pop domain
        have bodySupported := code.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs)
          args1 prog ss guards.2.2.1
        have entryCode : CostSupportedCode
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs none (WordSemStateFiniteExact.decClock source))).code := code
        have entryFrames : CodeFramesBounded
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs none (WordSemStateFiniteExact.decClock source))).code
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs none (WordSemStateFiniteExact.decClock source))).stackSize 92 := frames
        have postCode := entryCode.after_evaluate (post := post) bodySupported run
        have postFrames := entryFrames.after_evaluate (post := post) (wordCostSupported_noInstall prog bodySupported) entryCode.noInstallCode run
        have popFields := popEnvCodeGcFunClock post popped pop
        have poppedCode : CostSupportedCode popped.code := popFields.1 ▸ postCode
        have clock := evaluate_clock prog _ _ _ run
        have popClock := popEnv_clock post popped pop
        have popTermdep := popEnv_termdep post popped pop
        exact wordExecutionCost_correct ac price factor caps retCode
          (WordSemStateFiniteExact.setVars values returned popped) retSupported poppedCode (postFrames.after_popEnv (popped := popped) pop)
  | .call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2)), source, supported, code, frames => by
      have parts : wordCostSupported retCode = true ∧ wordCostSupported handlerCode = true := by
        simpa only [wordCostSupported,Bool.and_eq_true] using supported
      have retSupported := parts.1
      have handlerSupported := parts.2
      apply executedSimulation_returningHandler_fine _ price factor ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
        source frames (caps.handler values names retCode l1 l2 dest args handlerVar handlerCode h1 h2 source)
      · intro xs args1 prog ss envs guards nonzero
        exact wordExecutionCost_correct ac price factor caps prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))
          (code.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) args1 prog ss guards.2.2.1)
          code frames
      · intro xs args1 prog ss envs location returned post popped guards nonzero run valid pop domain
        have bodySupported := code.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs)
          args1 prog ss guards.2.2.1
        have entryCode : CostSupportedCode
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).code := code
        have entryFrames : CodeFramesBounded
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).code
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).stackSize 92 := frames
        have postCode := entryCode.after_evaluate (post := post) bodySupported run
        have postFrames := entryFrames.after_evaluate (post := post) (wordCostSupported_noInstall prog bodySupported) entryCode.noInstallCode run
        have popFields := popEnvCodeGcFunClock post popped pop
        have poppedCode : CostSupportedCode popped.code := popFields.1 ▸ postCode
        have clock := evaluate_clock prog _ _ _ run
        have popClock := popEnv_clock post popped pop
        have popTermdep := popEnv_termdep post popped pop
        exact wordExecutionCost_correct ac price factor caps retCode
          (WordSemStateFiniteExact.setVars values returned popped) retSupported poppedCode (postFrames.after_popEnv (popped := popped) pop)
      · intro xs args1 prog ss envs location value post guards nonzero run valid domain
        have bodySupported := code.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs)
          args1 prog ss guards.2.2.1
        have entryCode : CostSupportedCode
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).code := code
        have entryFrames : CodeFramesBounded
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).code
            (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).stackSize 92 := frames
        have clock := evaluate_clock prog _ _ _ run
        exact wordExecutionCost_correct ac price factor caps handlerCode
          (WordSemStateFiniteExact.setVar handlerVar value post) handlerSupported
          (entryCode.after_evaluate (post := post) bodySupported run)
          (entryFrames.after_evaluate (post := post) (wordCostSupported_noInstall prog bodySupported) entryCode.noInstallCode run)
  | .skip, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.skip) source supported
  | .tick, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.tick) source supported
  | .inst instruction, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.inst instruction) source supported
  | .move priority moves, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.move priority moves) source supported
  | .get register name, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.get register name) source supported
  | .set name expression, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.set name expression) source supported
  | .locValue register location, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.locValue register location) source supported
  | .return register values, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.return register values) source supported
  | .opCurrHeap operator dst src, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.opCurrHeap operator dst src) source supported
  | .ffi index ptr1 len1 ptr2 len2 names, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.ffi index ptr1 len1 ptr2 len2 names) source supported
  | .raise name, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.raise name) source supported
  | .break label, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.break label) source supported
  | .continue label, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.continue label) source supported
  | .mustTerminate body, source, supported, code, frames =>
      (refinedExecutedSimulation_mustTerminate ac body source).mono (Nat.zero_le _)
  | .alloc n names, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .storeConsts r1 r2 a off words, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .assign reg expression, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .store expression reg, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .install ptr len dptr dlen names, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .codeBufferWrite a b, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .dataBufferWrite a b, source, supported, code, frames => by
      simp only [wordCostSupported,refinedWordStackLeafBudget,Option.isSome_none,Bool.false_eq_true] at supported
  | .shareInst op reg expression, source, supported, code, frames =>
      fine_leaf_of_isSome ac price factor caps (.shareInst op reg expression) source supported
termination_by program source => (source.termdep,source.clock,sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try rcases clock with ⟨_,_⟩
    try rcases cutClock with ⟨_,_⟩
    try simp only [WordSemStateFiniteExact.decClock,WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.setVars,WordSemStateFiniteExact.setVar,pushEnv_clock,pushEnv_termdep,
      wordSemSTOP,true_and] at *
    omega

#print axioms wordExecutionCost_correct
end InitECandidate.Runtime.WordToStack
