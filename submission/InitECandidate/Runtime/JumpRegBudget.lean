import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderJumpReg

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- The concrete register-jump encoder has an exact one-instruction witness. -/
theorem jumpReg_encoder_budget (r : Nat)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.jumpReg r) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 1 ∧ encoderStepAt riscvTarget before (.jumpReg r) after ms n := by
  obtain ⟨n, count, run⟩ := Encoder.jumpReg_one_step r before after ms
    ⟨step, related⟩
  exact ⟨n, Nat.le_of_eq count, run⟩

/-- Concrete quantitative compiler step, through the authoritative target
clocked evaluator and its dispatcher. Every original guard is retained. -/
theorem jumpReg_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (r : Nat)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.jumpReg r)).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.jumpReg r)
        (asmUpd (.jumpReg r)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpReg r)).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 1 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.jumpReg r)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpReg r)).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 1 ∧ encoderStepAt mc.target before (.jumpReg r)
      (asmUpd (.jumpReg r)
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpReg r)).length) before) ms n := by
    rw [target]
    apply jumpReg_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.jumpReg r) h 1 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.jumpReg_step_evaluator_bounded
