import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderBranch
import InitECandidate.Runtime.EncoderBranchNearRegTest
import InitECandidate.Runtime.EncoderBranchNearImm
import InitECandidate.Runtime.EncoderBranchFarReg
import InitECandidate.Runtime.EncoderBranchFarRegTest
import InitECandidate.Runtime.EncoderBranchFarImm

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

theorem branch_encoder_budget (cmp : Cmp) (r : Nat) (right : HolRegImm 64) (offset : BitVec 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.jumpCmp cmp r right offset) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 3 ∧ encoderStepAt riscvTarget before (.jumpCmp cmp r right offset) after ms n := by
  by_cases near : -4092 ≤ offset.toInt ∧ offset.toInt ≤ 4095
  · cases right with
    | imm value =>
      exact Encoder.BranchNearImm.near_immediate_case cmp r value offset before after ms ⟨step, related⟩ near
    | reg other =>
      by_cases test : cmp = .test ∨ cmp = .notTest
      · exact Encoder.BranchNearRegTest.near_register_test_case cmp r other offset before after ms
          ⟨step, related⟩ near test
      · obtain ⟨n, count, run⟩ := Encoder.near_comparison_one_step cmp r other offset before after ms
          ⟨step, related⟩ near ⟨fun eq => test (Or.inl eq), fun eq => test (Or.inr eq)⟩
        exact ⟨n, by omega, run⟩
  · cases right with
    | imm value =>
      exact Encoder.BranchFarImm.far_immediate_case cmp r value offset before after ms ⟨step, related⟩ near
    | reg other =>
      by_cases test : cmp = .test ∨ cmp = .notTest
      · exact Encoder.BranchFarRegTest.far_register_test_case cmp r other offset before after ms
          ⟨step, related⟩ near test
      · exact Encoder.BranchFarReg.far_register_simple_case cmp r other offset before after ms
          ⟨step, related⟩ near ⟨fun eq => test (Or.inl eq), fun eq => test (Or.inr eq)⟩

theorem branch_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (cmp : Cmp) (r : Nat) (right : HolRegImm 64) (offset : BitVec 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.jumpCmp cmp r right offset)).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.jumpCmp cmp r right offset)
        (asmUpd (.jumpCmp cmp r right offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpCmp cmp r right offset)).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 3 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.jumpCmp cmp r right offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpCmp cmp r right offset)).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 3 ∧ encoderStepAt mc.target before (.jumpCmp cmp r right offset)
      (asmUpd (.jumpCmp cmp r right offset)
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.jumpCmp cmp r right offset)).length) before) ms n := by
    rw [target]
    apply branch_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.jumpCmp cmp r right offset) h 3 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.branch_step_evaluator_bounded
