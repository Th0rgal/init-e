import InitECandidate.Runtime.BinopBudget
import InitECandidate.Runtime.ShiftBudget
import InitECandidate.Runtime.DivBudget
import InitECandidate.Runtime.EncoderLongMul
import InitECandidate.Runtime.EncoderAddCarry
import InitECandidate.Runtime.EncoderAddOverflow
import InitECandidate.Runtime.EncoderSubOverflow

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Uniform bound for every arithmetic constructor admitted by the RISC-V target. -/
theorem arith_encoder_budget (operation : HolArith 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst (.arith operation)) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 16 ∧ encoderStepAt riscvTarget before (.inst (.arith operation)) after ms n := by
  cases operation with
  | binop op rd rs operand =>
    obtain ⟨n, bound, run⟩ := binop_encoder_budget op rd rs operand before after ms step related
    exact ⟨n, by omega, run⟩
  | shift op rd rs operand =>
    obtain ⟨n, bound, run⟩ := all_shift_encoder_budget op rd rs operand before after ms step related
    exact ⟨n, by omega, run⟩
  | div rd rs rt =>
    obtain ⟨n, bound, run⟩ := div_encoder_budget rd rs rt before after ms step related
    exact ⟨n, by omega, run⟩
  | longMul a b c d =>
    obtain ⟨n, bound, run⟩ := Encoder.longmul_bounded a b c d before after ms ⟨step, related⟩
    exact ⟨n, by omega, run⟩
  | addCarry a b c d =>
    exact Encoder.addcarry_bounded a b c d before after ms ⟨step, related⟩
  | addOverflow a b c d =>
    exact Encoder.addoverflow_bounded a b c d before after ms ⟨step, related⟩
  | subOverflow a b c d =>
    exact Encoder.suboverflow_bounded a b c d before after ms ⟨step, related⟩
  | longDiv a b c d e =>
    have valid := step.2.2.2.2.2.2
    simp [asmOkExact, asmInstOkExact, asmArithOkExact, riscvTarget, riscvConfig] at valid

theorem arith_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (operation : HolArith 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.inst (.arith operation))).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.inst (.arith operation))
        (asmUpd (.inst (.arith operation))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith operation))).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 16 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.inst (.arith operation))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith operation))).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 16 ∧ encoderStepAt mc.target before (.inst (.arith operation))
      (asmUpd (.inst (.arith operation))
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.arith operation))).length) before) ms n := by
    rw [target]
    apply arith_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.inst (.arith operation)) h 16 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.arith_step_evaluator_bounded
