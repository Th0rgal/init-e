import InitECandidate.Runtime.EncoderRorRegister
import InitECandidate.Runtime.EncoderRorImmediate
import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderShift
import InitECandidate.Runtime.EncoderShiftLslRegister
import InitECandidate.Runtime.EncoderShiftLsrRegister
import InitECandidate.Runtime.EncoderShiftLsrImmediate
import InitECandidate.Runtime.EncoderShiftAsrRegister
import InitECandidate.Runtime.EncoderShiftAsrImmediate


namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Every non-rotating shift has a one-native-instruction witness. -/
theorem shift_encoder_budget (op : Flapjack.Shift) (rd rs : Nat) (operand : HolRegImm 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst (.arith (.shift op rd rs operand))) after)
    (related : targetStateRel riscvTarget before ms) (notRotate : op ≠ .ror) :
    ∃ n, n + 1 ≤ 1 ∧ encoderStepAt riscvTarget before (.inst (.arith (.shift op rd rs operand))) after ms n := by
  cases op <;> cases operand
  · obtain ⟨n, count, run⟩ := Encoder.shiftLslRegister_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.lsl_immediate_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.shiftLsrRegister_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.shiftLsrImmediate_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.shiftAsrRegister_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.shiftAsrImmediate_one_step rd rs _ before after ms ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  all_goals exact False.elim (notRotate rfl)

/-- Concrete quantitative compiler step, through the authoritative target
clocked evaluator and its dispatcher. Every original guard is retained. -/
theorem shift_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (op : Flapjack.Shift) (rd rs : Nat) (operand : HolRegImm 64)
    (notRotate : op ≠ .ror)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.inst (.arith (.shift op rd rs operand)))
        (asmUpd (.inst (.arith (.shift op rd rs operand)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 1 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.inst (.arith (.shift op rd rs operand)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 1 ∧ encoderStepAt mc.target before (.inst (.arith (.shift op rd rs operand)))
      (asmUpd (.inst (.arith (.shift op rd rs operand)))
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) ms n := by
    rw [target]
    apply shift_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
    · exact notRotate
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.inst (.arith (.shift op rd rs operand))) h 1 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

/-- Uniform encoder bound for all eight shift forms, including rotate-right. -/
theorem all_shift_encoder_budget (op : Flapjack.Shift) (rd rs : Nat) (operand : HolRegImm 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst (.arith (.shift op rd rs operand))) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 5 ∧ encoderStepAt riscvTarget before
      (.inst (.arith (.shift op rd rs operand))) after ms n := by
  by_cases rotate : op = .ror
  · subst op
    cases operand with
    | reg other =>
      exact Encoder.RorRegister.ror_register_bounded rd rs other before after ms ⟨step, related⟩
    | imm value =>
      exact Encoder.RorImmediate.ror_immediate_bounded rd rs value before after ms ⟨step, related⟩
  · obtain ⟨n, bound, run⟩ := shift_encoder_budget op rd rs operand before after ms step related rotate
    exact ⟨n, by omega, run⟩

theorem all_shift_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (op : Flapjack.Shift) (rd rs : Nat) (operand : HolRegImm 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.inst (.arith (.shift op rd rs operand)))
        (asmUpd (.inst (.arith (.shift op rd rs operand)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 5 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.inst (.arith (.shift op rd rs operand)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 5 ∧ encoderStepAt mc.target before (.inst (.arith (.shift op rd rs operand)))
      (asmUpd (.inst (.arith (.shift op rd rs operand)))
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith (.shift op rd rs operand)))).length) before) ms n := by
    rw [target]
    apply all_shift_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.inst (.arith (.shift op rd rs operand))) h 5 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.shift_step_evaluator_bounded

#print axioms InitECandidate.Runtime.all_shift_step_evaluator_bounded
