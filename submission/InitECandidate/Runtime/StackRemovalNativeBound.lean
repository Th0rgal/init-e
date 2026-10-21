import InitECandidate.Runtime.StackRemovalExecutedCorrect
import InitECandidate.Runtime.StackExecutionNativeGap
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

theorem RemovalCostPost.terminal_ffi {F : Type} {jump bounds pointer}
    {sourcePost targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {outcome : HolOutcome}
    (post : RemovalCostPost jump bounds pointer sourcePost targetPost (some result))
    (terminal : executionKindOfResult (some result) = .terminal result outcome) :
    targetPost.ffi = sourcePost.ffi := by
  cases result <;> try (cases terminal)
  case halt value => exact post
  case finalFFI event => exact post

/-- Stack removal and native extraction composed. The compiled run and its
cost bound are derived here. Only the ordinary flattening/encoding/machine
relations remain at the subsequent compiler boundary; no native run or
whole-execution budget is assumed. -/
theorem stackRemoval_native_bound {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (program : HolProg 64) (source sourcePost targetStack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : StackSemResult 64) (outcome : HolOutcome) (pointer : Nat)
    (sourceRun : StackSemEvaluate.evaluate (program, source) = (some result, sourcePost))
    (terminal : executionKindOfResult (some result) = .terminal result outcome)
    (supported : removalSupported program = true) (global : RemovalCodeSupported source.code)
    (oracle : EmptyInstallOracle source)
    (relatedStack : StackRemove.stateRelHOL false bounds pointer source targetStack)
    (registers : StackProps.regBound program pointer)
    (compiledSupported : executionSupported (StackRemove.comp false bounds pointer program) = true)
    (compiledGlobal : ExecutionCodeSupported targetStack.code)
    (compiledScope : ExecutionLabelScope targetStack.code (StackRemove.comp false bounds pointer program)) :
    ∃ clock removedPost,
      StackSemEvaluate.evaluate (StackRemove.comp false bounds pointer program,
        {targetStack with clock := clock + targetStack.clock}) = (some result, removedPost) ∧
      removedPost.ffi = sourcePost.ffi ∧
      ∀ (flag : Bool) (sectionId labelId : Nat) (continues breaks : List Nat)
        (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64),
      encodedLineWords encoded ≤ gap →
      FlattenHyps (StackRemove.comp false bounds pointer program)
        {targetStack with clock := clock + targetStack.clock} flag (some result) removedPost
        sectionId labelId continues breaks start →
      ∀ (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
        (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64) (machine : RiscV.L3.riscv_state),
      mc.target = Compiler.Encoders.RiscV.Target.riscvTarget →
      Compiler.Encoders.AsmProps.encoderCorrect mc.target →
      Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine →
      Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start →
      ∃ count native,
        count ≤ stackExecutionCost (fun p _ => removalLocalPrice gap bounds p) program source + 17 ∧
        evaluateTargetHOL mc start.ffi count machine = (.halt outcome, native, sourcePost.ffi) := by
  have valid : ExecutionResultValid source.code (some result) := executionKindOfResult_terminal_valid terminal
  obtain ⟨clock, removedPost, removedRun, postRelation, cost⟩ :=
    stackRemoval_cost_correct gap bounds program source supported global oracle sourcePost targetStack
      (some result) pointer ⟨sourceRun, valid.nonerror, relatedStack, registers⟩
  have ffiEq := postRelation.terminal_ffi terminal
  refine ⟨clock, removedPost, removedRun, ffiEq, ?_⟩
  intro flag sectionId labelId continues breaks start encoded gapBound hyps mc labs base asm machine target encoder related tie
  obtain ⟨count, native, nativeBound, nativeRun⟩ := native_with_gap_of_evaluate
    flag removedPost sectionId labelId continues breaks start encoded gap gapBound hyps removedRun
    compiledSupported compiledGlobal compiledScope terminal mc labs base asm machine target encoder related tie
  refine ⟨count, native, nativeBound.trans (Nat.add_le_add_right cost 17), ?_⟩
  simpa only [ffiEq] using nativeRun

#print axioms stackRemoval_native_bound
end InitECandidate.Runtime.StackToLab
