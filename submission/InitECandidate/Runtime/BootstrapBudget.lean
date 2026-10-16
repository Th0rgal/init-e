import InitECandidate.Runtime.AsmBudget
import InitECandidate.Runtime.EncoderLoc
import InitECandidate.Runtime.EncoderMemory
import InitECandidate.Runtime.EncoderConst
import InitECandidate.Runtime.EncoderShift
import InitECandidate.Runtime.EncoderBinop
import InitECandidate.Runtime.EncoderBranch
import InitECandidate.Runtime.EncoderJump
import InitECandidate.Proofs.BootstrapTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition InitECandidate.Proofs.BootstrapTrace

/-- Syntactic bootstrap subset whose emitted instructions have ceilings of two.
Constant values and branch forms are checked, rather than assumed from testing. -/
def bootstrapSupported : HolAsm 64 → Bool
  | .loc _ _ => true
  | .inst (.const _ value) => value == 161 || value == 2015 || value == 63
  | .inst (.arith (.shift .lsl _ _ (.imm _))) => true
  | .inst (.arith (.binop _ _ _ (.imm _))) => true
  | .inst (.mem _ _ _) => true
  | .jump offset => decide (-1048576 ≤ offset.toInt ∧ offset.toInt ≤ 1048575)
  | .jumpCmp cmp _ (.reg _) offset =>
      decide (-4092 ≤ offset.toInt ∧ offset.toInt ≤ 4095 ∧ cmp ≠ .test ∧ cmp ≠ .notTest)
  | _ => false

theorem bootstrap_encoder_budget (instruction : HolAsm 64)
    (before afterState : AsmState 64) (machine : riscv_state)
    (supported : bootstrapSupported instruction = true)
    (step : asmStep riscvTarget.config before instruction afterState)
    (related : targetStateRel riscvTarget before machine) :
    ∃ n, n + 1 ≤ 2 ∧ encoderStepAt riscvTarget before instruction afterState machine n := by
  cases instruction with
  | loc reg offset =>
    obtain ⟨n, count, run⟩ := Encoder.loc_encoder_correct_two_steps reg offset before afterState machine ⟨step, related⟩
    exact ⟨n, Nat.le_of_eq count, run⟩
  | jump offset =>
    have range := of_decide_eq_true supported
    obtain ⟨n, count, run⟩ := Encoder.near_jump_one_step offset before afterState machine ⟨step, related⟩ range
    exact ⟨n, by omega, run⟩
  | jumpCmp cmp reg right offset =>
    cases right with
    | imm _ => simp [bootstrapSupported] at supported
    | reg reg2 =>
      have range := of_decide_eq_true supported
      obtain ⟨n, count, run⟩ := Encoder.near_comparison_one_step cmp reg reg2 offset before afterState machine
        ⟨step, related⟩ ⟨range.1, range.2.1⟩ ⟨range.2.2.1, range.2.2.2⟩
      exact ⟨n, by omega, run⟩
  | call _ => simp [bootstrapSupported] at supported
  | jumpReg _ => simp [bootstrapSupported] at supported
  | inst instruction =>
    cases instruction with
    | skip => simp [bootstrapSupported] at supported
    | const reg value =>
      obtain ⟨n, count, run⟩ := Encoder.const_encoder_correct_count reg value before afterState machine ⟨step, related⟩
      have values : value = 161 ∨ value = 2015 ∨ value = 63 := by
        simpa [bootstrapSupported, Bool.or_eq_true, or_assoc] using supported
      have size : (riscvAst (.inst (.const reg value))).length ≤ 2 := by
        rcases values with rfl | rfl | rfl <;> decide_cbv
      exact ⟨n, count.le.trans size, run⟩
    | mem op reg addr =>
      cases addr with
      | addr base offset =>
        obtain ⟨n, count, run⟩ := Encoder.mem_encoder_correct_one_step op reg base offset before afterState machine ⟨step, related⟩
        exact ⟨n, by omega, run⟩
    | arith arithmetic =>
      cases arithmetic with
      | binop op reg src right =>
        cases right with
        | reg _ => simp [bootstrapSupported] at supported
        | imm value =>
          obtain ⟨n, count, run⟩ := Encoder.binop_immediate_one_step op reg src value before afterState machine ⟨step, related⟩
          exact ⟨n, by omega, run⟩
      | shift op reg src right =>
        cases op <;> cases right <;> try { simp [bootstrapSupported] at supported }
        obtain ⟨n, count, run⟩ := Encoder.lsl_immediate_one_step reg src _ before afterState machine ⟨step, related⟩
        exact ⟨n, by omega, run⟩
      | div _ _ _ => simp [bootstrapSupported] at supported
      | longMul _ _ _ _ => simp [bootstrapSupported] at supported
      | longDiv _ _ _ _ _ => simp [bootstrapSupported] at supported
      | addCarry _ _ _ _ => simp [bootstrapSupported] at supported
      | addOverflow _ _ _ _ => simp [bootstrapSupported] at supported
      | subOverflow _ _ _ _ => simp [bootstrapSupported] at supported

theorem full_bootstrap_supported : fullBootstrapCode.all bootstrapSupported = true := by
  decide_cbv

/-- Every local timing certificate for the real bootstrap is discharged. -/
theorem full_bootstrap_budgets : TraceBudgets (fun _ => 2) fullBootstrapCode initialAsm := by
  have general : ∀ code state, code.all bootstrapSupported = true → Checked code state →
      TraceBudgets (fun _ => 2) code state := by
    intro code
    induction code with
    | nil => intro state _ _; trivial
    | cons instruction rest ih =>
      intro state supported checks
      simp only [List.all_cons, Bool.and_eq_true] at supported
      exact ⟨fun machine related => bootstrap_encoder_budget instruction state
        (after state instruction) machine supported.1 checks.1 related,
        ih (after state instruction) supported.2 checks.2⟩
  exact general _ _ full_bootstrap_supported full_checked

theorem traceCost_two (code : List (HolAsm 64)) :
    traceCost (fun _ => 2) code = 2 * code.length := by
  induction code with
  | nil => rfl
  | cons instruction rest ih => simp [traceCost, ih, Nat.mul_add, Nat.add_comm]

/-- Uniform bootstrap overhead in the authoritative target evaluator.
46240 is conservative; no measured Spike count is used in the proof. -/
theorem full_bootstrap_bounded {σ : Type} (io : HolFfiState σ) (machine : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm machine) :
    ∃ count post, count ≤ 46240 ∧
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) machine =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨count, post, bound, shift, related⟩ := checked_trace_evaluator_bounded
    baselineMachineConfig rfl rfl (fun _ => 2) fullBootstrapCode initialAsm
    full_checked full_guards full_bootstrap_budgets machine io initial
  refine ⟨count, post, ?_, shift, ?_⟩
  · simpa only [traceCost_two, full_length] using bound
  · simpa only [full_endpoint] using related

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.full_bootstrap_bounded
