import InitECandidate.Runtime.LabExtract
import InitECandidate.Runtime.LabWeightedMixedTrace
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Reweight the same actual instruction execution using visited expansions. -/
theorem instructionTrace_weighted {F : Type} {start final : LabSem.State 64 Config F}
    {length : Nat} (code : LabProgHOL 64) (trace : InstructionTrace start final length) :
    ∃ work, WeightedInstructionTrace code start final work := by
  induction trace with
  | nil state => exact ⟨0, .nil state⟩
  | step state final i bytes n length clock fetch success rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .step state final i bytes n work clock fetch success tail⟩
  | jump state final label pc w bytes n length clock fetch destination rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .jump state final label pc w bytes n work clock fetch destination tail⟩
  | jumpReg state final r n1 n2 pc bytes n length clock fetch register destination rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .jumpReg state final r n1 n2 pc bytes n work clock fetch register destination tail⟩
  | branchTaken state final cmp r operand label pc w bytes n length clock fetch chosen destination rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .branchTaken state final cmp r operand label pc w bytes n work clock fetch chosen destination tail⟩
  | branchFallthrough state final cmp r operand label w bytes n length clock fetch chosen rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .branchFallthrough state final cmp r operand label w bytes n work clock fetch chosen tail⟩
  | locValue state final r label pc w bytes n length clock fetch destination rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .locValue state final r label pc w bytes n work clock fetch destination tail⟩

theorem mixedTrace_weighted {F : Type} {start final : LabSem.State 64 Config F}
    {length : Nat} (code : LabProgHOL 64) (trace : MixedTrace start final length) :
    ∃ work, WeightedMixedTrace code start final work := by
  induction trace with
  | nil state => exact ⟨0, .nil state⟩
  | ordinary start middle final length restLength segment rest ih =>
    obtain ⟨firstWork, first⟩ := instructionTrace_weighted code segment
    obtain ⟨restWork, tail⟩ := ih
    exact ⟨_, .ordinary start middle final firstWork restWork first tail⟩
  | ffi state final name w bytes n len start len2 start2 conf bytes2 n1 n2 pc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .ffi state final name w bytes n len start len2 start2 conf bytes2 n1 n2 pc
      newFfi newBytes work clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call tail⟩
  | shared state final m r base off bytes n ffi returned next length clock fetch operation rest ih =>
    obtain ⟨work, tail⟩ := ih
    exact ⟨_, .shared state final m r base off bytes n ffi returned next work clock fetch operation tail⟩

/-- Successful supported evaluation supplies its own locally weighted trace.
No source trace, native execution, or numerical runtime bound is assumed. -/
theorem extract_supported_weighted_trace {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (code : LabProgHOL 64) (supported : SupportedCode state.code)
    (evaluated : evaluate state = (.halt outcome, post)) :
    ∃ work, WeightedMixedTrace code state post work ∧ Terminal post outcome := by
  obtain ⟨length, trace, terminal⟩ := extract_supported_trace state post outcome supported evaluated
  obtain ⟨work, weighted⟩ := mixedTrace_weighted code trace
  exact ⟨work, weighted, terminal⟩

/-- Local weighted transfer for actual evaluator runs, including ordinary halt,
terminal FFI and terminal shared-memory outcomes. Original relations remain. -/
theorem supported_evaluation_weighted_native_bound {F : Type}
    (state post : LabSem.State 64 Config F) (outcome : HolOutcome)
    (supported : SupportedCode state.code) (evaluated : evaluate state = (.halt outcome, post))
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) state asm machine) (tie : oracleTie mc machine state) :
    ∃ work count native, WeightedMixedTrace code state post work ∧ count ≤ work + 17 ∧
      evaluateTargetHOL mc state.ffi count machine = (.halt outcome, native, post.ffi) := by
  obtain ⟨work, trace, terminal⟩ := extract_supported_weighted_trace state post outcome code supported evaluated
  obtain ⟨firstCount, middle, middleAsm, finalConfig, firstBound, finalTarget,
      finalEncoder, firstRun, middleRel, middleTie⟩ :=
    weightedMixedTrace_bounded code trace mc labs p asm machine target encoder related tie
  obtain ⟨lastCount, native, lastBound, lastRun⟩ :=
    terminal_native terminal finalConfig code labs p middleAsm middle finalTarget finalEncoder middleRel
  refine ⟨work, lastCount + firstCount, native, trace, by omega, ?_⟩
  rw [firstRun, lastRun]

#print axioms supported_evaluation_weighted_native_bound
#print axioms extract_supported_weighted_trace
end InitECandidate.Runtime.LabToTarget
