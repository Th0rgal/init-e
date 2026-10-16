import InitECandidate.Runtime.InstBudget
import InitECandidate.Runtime.BranchBudget
import InitECandidate.Runtime.CallBudget
import InitECandidate.Runtime.JumpBudget
import InitECandidate.Runtime.JumpRegBudget
import InitECandidate.Runtime.LocBudget
import InitECandidate.Runtime.AsmBudget

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition

/-- Every valid RISC-V assembly constructor takes at most sixteen native steps. -/
theorem asm_encoder_budget (instruction : HolAsm 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before instruction after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 16 ∧ encoderStepAt riscvTarget before instruction after ms n := by
  cases instruction with
  | inst value => exact inst_encoder_budget value before after ms step related
  | jump offset =>
    obtain ⟨n, bound, run⟩ := jump_encoder_budget offset before after ms step related
    exact ⟨n, by omega, run⟩
  | jumpCmp cmp r right offset =>
    obtain ⟨n, bound, run⟩ := branch_encoder_budget cmp r right offset before after ms step related
    exact ⟨n, by omega, run⟩
  | call offset =>
    obtain ⟨n, bound, run⟩ := call_encoder_budget offset before after ms step related
    exact ⟨n, by omega, run⟩
  | jumpReg r =>
    obtain ⟨n, bound, run⟩ := jumpReg_encoder_budget r before after ms step related
    exact ⟨n, by omega, run⟩
  | loc r offset =>
    obtain ⟨n, bound, run⟩ := loc_encoder_budget r offset before after ms step related
    exact ⟨n, by omega, run⟩

/-- Quantitative witnesses are now derived from checked execution, for any
assembly trace; no separate per-instruction budget hypothesis is needed. -/
theorem checked_trace_uniform_budgets (code : List (HolAsm 64)) (state : AsmState 64)
    (checks : Checked code state) : TraceBudgets (fun _ => 16) code state := by
  induction code generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
    constructor
    · intro machine related
      apply asm_encoder_budget instruction state (after state instruction) machine
      · simpa only [riscvTarget, riscvConfig_encode, after] using checks.1
      · exact related
    · exact ih (after state instruction) checks.2

theorem traceCost_uniform (code : List (HolAsm 64)) :
    traceCost (fun _ => 16) code = 16 * code.length := by
  induction code with
  | nil => rfl
  | cons instruction rest ih => simp [traceCost, ih, Nat.mul_add, Nat.add_comm]

/-- A complete checked assembly trace needs at most sixteen native steps per
assembly instruction, preserving the actual evaluator endpoint and FFI state. -/
theorem checked_trace_uniform_bound {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (code : List (HolAsm 64)) (state : AsmState 64)
    (checks : Checked code state) (guards : EvaluatorGuards mc code state)
    (machine : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget state machine) :
    ∃ count post, count ≤ 16 * code.length ∧
      (∀ clock, evaluateTargetHOL mc io (count + clock) machine =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code state) post := by
  simpa only [traceCost_uniform] using checked_trace_evaluator_bounded mc target identity
    (fun _ => 16) code state checks guards (checked_trace_uniform_budgets code state checks)
    machine io related

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.checked_trace_uniform_bound
