import InitECandidate.Runtime.WordEntryExecutedCost
import InitECandidate.Runtime.WordEntryTerminalResult
import InitECandidate.Runtime.StackRefinedRemovalNativeBound
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open InitECandidate.Runtime.FineCost InitECandidate.Runtime.StackToLab

/-- Native continuation contract at the entry compiler boundary. It keeps
all removal, flattening and machine-state premises explicit and is a result
to prove, never an assumed native execution or cost bound. -/
def EntryNativeCostPost {F : Type} (start : Nat)
    (stackSource stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome) (budget : Nat) : Prop :=
∀ (targetStack : StackSemStateFiniteExact 64 LabToTarget.Config F) (pointer : Nat),
      StackRemove.stateRelHOL false riscvConfig.addrOffset pointer
        stackSource targetStack →
      StackProps.regBound (width := 64) (.call none (.inl start) none) pointer →
      executionSupported (StackRemove.comp false riscvConfig.addrOffset pointer
        (.call none (.inl start) none)) = true →
      ExecutionCodeSupported targetStack.code →
      ExecutionLabelScope targetStack.code (StackRemove.comp false riscvConfig.addrOffset pointer
        (.call none (.inl start) none)) →
      ∃ clock removedPost,
        StackSemEvaluate.evaluate (StackRemove.comp false riscvConfig.addrOffset pointer
          (.call none (.inl start) none),{targetStack with clock := clock+targetStack.clock}) =
          (some result,removedPost) ∧
        removedPost.ffi = stackPost.ffi ∧
        ∀ (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
          (labStart : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64),
        encodedLineWords encoded ≤ 6 →
        FlattenHyps (StackRemove.comp false riscvConfig.addrOffset pointer (.call none (.inl start) none))
          {targetStack with clock := clock+targetStack.clock} flag (some result) removedPost
          sectionId labelId continues breaks labStart →
        ∀ (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
          (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64) (machine : RiscV.L3.riscv_state),
        mc.target = riscvTarget → Compiler.Encoders.AsmProps.encoderCorrect mc.target →
        LabToTarget.stateRel (mc,encoded,labs,base) labStart asm machine →
        LabToTarget.oracleTie mc machine labStart →
        ∃ count native,
          count ≤ budget+17 ∧
          evaluateTargetHOL mc labStart.ffi count machine = (.halt outcome,native,stackPost.ffi)

/-- Concrete Word-entry work bounds native execution after StackRemove.
The Word-to-Stack run and its cost are constructed. Remaining hypotheses are
the ordinary removal, flattening, encoding and machine-state relations, plus
the terminal classification of the constructed compiler result. -/
theorem wordEntry_native_execution_cost {F : Type} (ac : AsmConfigExact 64)
    (start forbidden : Nat)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (sourceResult : Option (WordSemResult 64))
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (code : CostSupportedCode source.code)
    (frames : CodeFramesBounded source.code source.stackSize 92)
    (sourceRun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) source =
      (sourceResult,sourcePost))
    (notError : sourceResult ≠ some .error)
    (related : stateRel ac 22 0 0 source target lens 0)
    (closed : directCallsAvoid forbidden (.call none (.inl start) none) = true)
    (global : AvoidingRemovalCode forbidden target.code)
    (oracle : EmptyInstallOracle target) :
    ∃ extra stackPost output,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {target with clock := target.clock+extra}) = (output,stackPost) ∧
      compCorrectResult ac 22 0 0 source sourcePost stackPost sourceResult output lens ∧
      ∀ (result : StackSemResult 64) (outcome : HolOutcome),
      output = some result → executionKindOfResult (some result) = .terminal result outcome →
      EntryNativeCostPost start {target with clock := target.clock+extra} stackPost result outcome
        (wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none) source) := by
  obtain ⟨extra,stackPost,output,run,contract,cost⟩ := compCall_refined_execution_cost ac start source
    sourceResult sourcePost target lens code frames sourceRun notError related
  refine ⟨extra,stackPost,output,run,contract,?_⟩
  intro result outcome same terminal targetStack pointer removal registers compiledSupported compiledGlobal compiledScope
  rw [same] at run
  obtain ⟨clock,removedPost,removedRun,ffiEq,nativeBound⟩ :=
    refinedStackRemoval_native_bound_reachable forbidden 6 riscvConfig.addrOffset
      (.call none (.inl start) none) {target with clock := target.clock+extra} stackPost targetStack
      result outcome pointer run terminal (by simp [removalSupported]) closed global oracle removal registers
      compiledSupported compiledGlobal compiledScope
  refine ⟨clock,removedPost,removedRun,ffiEq,?_⟩
  intro flag sectionId labelId continues breaks labStart encoded gap hyps mc labs base asm machine targetEq encoder relation tie
  obtain ⟨count,native,bound,nativeRun⟩ := nativeBound flag sectionId labelId continues breaks labStart encoded
    gap hyps mc labs base asm machine targetEq encoder relation tie
  exact ⟨count,native,bound.trans (Nat.add_le_add_right cost 17),nativeRun⟩

/-- Source final-FFI termination discharges the native terminal-result
condition while retaining the specified resource-limit alternative. -/
theorem wordEntry_finalFFI_native_execution_cost {F : Type} (ac : AsmConfigExact 64)
    (start forbidden : Nat)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (event : HolFinalEvent) (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (code : CostSupportedCode source.code) (frames : CodeFramesBounded source.code source.stackSize 92)
    (sourceRun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) source =
      (some (.finalFfi event),sourcePost))
    (related : stateRel ac 22 0 0 source target lens 0)
    (closed : directCallsAvoid forbidden (.call none (.inl start) none) = true)
    (global : AvoidingRemovalCode forbidden target.code) (oracle : EmptyInstallOracle target) :
    ∃ extra stackPost result outcome,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {target with clock := target.clock+extra}) = (some result,stackPost) ∧
      compCorrectResult ac 22 0 0 source sourcePost stackPost (some (.finalFfi event)) (some result) lens ∧
      executionKindOfResult (some result) = .terminal result outcome ∧
      EntryNativeCostPost start {target with clock := target.clock+extra} stackPost result outcome
        (wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none) source) := by
  obtain ⟨extra,stackPost,output,run,contract,native⟩ := wordEntry_native_execution_cost ac start forbidden source
    sourcePost (some (.finalFfi event)) target lens code frames sourceRun (by simp) related closed global oracle
  obtain ⟨result,outcome,same,terminal⟩ := compCorrectResult_finalFFI_terminal ac 22 0 0 source sourcePost
    stackPost event output lens contract
  have nativeCost := native result outcome same terminal
  rw [same] at run contract
  exact ⟨extra,stackPost,result,outcome,run,contract,terminal,nativeCost⟩

#print axioms EntryNativeCostPost
#print axioms wordEntry_native_execution_cost
#print axioms wordEntry_finalFFI_native_execution_cost
end InitECandidate.Runtime.WordToStack
