import InitECandidate.Runtime.StackExecutionTraceRiscV
import InitECandidate.Runtime.StackExecutionComplete
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- Actual supported terminal evaluator runs compile to a finite RISC-V halt.
The only quantitative premises are local encoding-price inequalities. -/
theorem native_of_evaluate {F : Type}
    {program : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {outcome : HolOutcome} {price : ExecutionLocalPrice F}
    (caps : LocalNativeCaps price)
    (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps program source flag (some result) post sectionId labelId continues breaks start)
    (run : StackSemEvaluate.evaluate (program, source) = (some result, post))
    (valid : ExecutionResultValid source.code (some result))
    (supported : executionSupported program = true)
    (global : ExecutionCodeSupported source.code)
    (scope : ExecutionLabelScope source.code program)
    (terminal : executionKindOfResult (some result) = .terminal result outcome)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start) :
    ∃ count native, count ≤ stackExecutionCost (fun p s => price p s encoded) program source + 17 ∧
      evaluateTargetHOL mc start.ffi count machine = (.halt outcome, native, post.ffi) := by
  have trace := executionTrace_of_evaluate program source (some result) post run valid supported global scope
  rw [terminal] at trace
  exact trace.native caps flag post sectionId labelId continues breaks start encoded hyps
    mc labs base asm machine target encoder related tie

#print axioms native_of_evaluate
end InitECandidate.Runtime.StackToLab
