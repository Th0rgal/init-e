import InitECandidate.Runtime.StackExecutionTraceNative
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

/-- The recursive semantic derivation yields an actual finite RISC-V halt,
within its independently defined executed Stack cost plus one terminal ceiling.
Original compilation, target, encoder and oracle relations stay explicit. -/
theorem ExecutionTrace.native {F : Type}
    {program : HolProg 64} {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {result : StackSemResult 64} {outcome : HolOutcome} {price : ExecutionLocalPrice F}
    (caps : LocalNativeCaps price)
    (flag : Bool) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (sectionId labelId : Nat) (continues breaks : List Nat)
    (start : LabSem.State 64 LabToTarget.Config F) (encoded : LabProgHOL 64)
    (hyps : FlattenHyps program source flag (some result) post sectionId labelId continues breaks start)
    (trace : ExecutionTrace source program (.terminal result outcome) post)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (labs : Spt (Spt Nat)) (base : BitVec 64) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (target : mc.target = Compiler.Encoders.RiscV.Target.riscvTarget)
    (encoder : Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (related : Flapjack.Compiler.Backend.LabToTarget.stateRel (mc, encoded, labs, base) start asm machine)
    (tie : Flapjack.Compiler.Backend.LabToTarget.oracleTie mc machine start) :
    ∃ count native, count ≤ stackExecutionCost (fun p s => price p s encoded) program source + 17 ∧
      evaluateTargetHOL mc start.ffi count machine = (.halt outcome, native, post.ffi) := by
  have bound : TerminalWeightedFlatten program source result outcome (executionCostPrice price program source) :=
    trace.bound caps
  simpa only [executionCostPrice] using bound.native flag post sectionId labelId continues breaks start encoded
    hyps mc labs base asm machine target encoder related tie

#print axioms ExecutionTrace.native
end InitECandidate.Runtime.StackToLab
