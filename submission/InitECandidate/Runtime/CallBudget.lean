import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderCallNear
import InitECandidate.Runtime.EncoderCallFar

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Every valid direct call takes at most two native instructions. -/
theorem call_encoder_budget (offset : BitVec 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.call offset) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 2 ∧ encoderStepAt riscvTarget before (.call offset) after ms n := by
  by_cases near : -1048576 ≤ offset.toInt ∧ offset.toInt ≤ 1048575
  · obtain ⟨n, count, run⟩ := Encoder.CallNear.call_near_count offset before after ms ⟨step, related⟩ near
    exact ⟨n, by omega, run⟩
  · obtain ⟨n, count, run⟩ := Encoder.CallFar.call_far_count offset before after ms ⟨step, related⟩ near
    exact ⟨n, Nat.le_of_eq count, run⟩

/-- Concrete quantitative compiler step, through the authoritative target
clocked evaluator and its dispatcher. Every original guard is retained. -/
theorem call_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (offset : BitVec 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.call offset)).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.call offset)
        (asmUpd (.call offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.call offset)).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 2 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.call offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.call offset)).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 2 ∧ encoderStepAt mc.target before (.call offset)
      (asmUpd (.call offset)
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.call offset)).length) before) ms n := by
    rw [target]
    apply call_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.call offset) h 2 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.call_step_evaluator_bounded
