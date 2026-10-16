import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Proofs.BootstrapAsmComposition

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition

/-- Sum of native instruction ceilings, including expansion of pseudo-ops. -/
def traceCost (cost : HolAsm 64 → Nat) : List (HolAsm 64) → Nat
  | [] => 0
  | instruction :: rest => cost instruction + traceCost cost rest

/-- Quantitative encoder certificates at every *calculated* assembler state.
These are stronger than unbounded encoder correctness and must be discharged
by the concrete constructor proofs, not inferred from an existential count. -/
noncomputable def TraceBudgets (cost : HolAsm 64 → Nat) :
    List (HolAsm 64) → AsmState 64 → Prop
  | [], _ => True
  | instruction :: rest, state =>
      (∀ machine, targetStateRel riscvTarget state machine →
        ∃ n, n + 1 ≤ cost instruction ∧
          encoderStepAt riscvTarget state instruction (after state instruction) machine n) ∧
      TraceBudgets cost rest (after state instruction)

/-- Checked assembler traces lift to *bounded* target evaluator prefixes.
The endpoint, dispatcher, interference shift and FFI state are the same as in
Flapjack's original simulation; the native-count ceiling is additionally retained. -/
theorem checked_trace_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (cost : HolAsm 64 → Nat) (code : List (HolAsm 64)) (state : AsmState 64)
    (checks : Checked code state) (guards : EvaluatorGuards mc code state)
    (budgets : TraceBudgets cost code state)
    (machine : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget state machine) :
    ∃ count post, count ≤ traceCost cost code ∧
      (∀ clock, evaluateTargetHOL mc io (count + clock) machine =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code state) post := by
  induction code generalizing state machine with
  | nil =>
    exact ⟨0, machine, Nat.le_refl _, fun _ => by simp only [Nat.zero_add], related⟩
  | cons instruction rest ih =>
    have interference : interferenceOk mc.nextInterfer (mc.target.proj state.memDomain) := by
      intro index machine
      rw [identity]
    have quantified : ∃ n, n + 1 ≤ cost instruction ∧
        encoderStepAt mc.target state instruction (after state instruction) machine n := by
      rw [target]
      exact budgets.1 machine related
    have hypotheses : encoderCorrect mc.target ∧ mc.progAddresses = state.memDomain ∧
        ffiEntryPcsDisjoint mc state (mc.target.config.encode instruction).length ∧
        interferenceOk mc.nextInterfer (mc.target.proj state.memDomain) ∧
        asmStep mc.target.config state instruction
          (asmUpd instruction (state.pc + BitVec.ofNat 64
            (mc.target.config.encode instruction).length) state) ∧
        targetStateRel mc.target state machine := by
      refine ⟨?_, guards.1, ?_, interference, ?_, ?_⟩
      · rw [target]
        exact Flapjack.RiscV.TargetProof.riscv_encoder_correct
      · simpa only [target, riscvTarget, riscvConfig_encode] using guards.2.1
      · simpa only [target, riscvTarget, riscvConfig_encode, after] using checks.1
      · simpa only [target] using related
    obtain ⟨firstCount, middle, firstBound, firstRun⟩ :=
      asmStepImpEvaluate_bounded mc state machine io instruction hypotheses
        (cost instruction) (by simpa only [target, riscvTarget, riscvConfig_encode, after]
          using quantified)
    have middleRelated : targetStateRel riscvTarget (after state instruction) middle := by
      simpa only [target, riscvTarget, riscvConfig_encode, after] using (firstRun 0).2.2.1
    have shifted := shiftInterfer_identity mc identity firstCount
    have firstShift : ∀ clock, evaluateTargetHOL mc io (clock + firstCount) machine =
        evaluateTargetHOL mc io clock middle := by
      intro clock
      simpa only [shifted] using (firstRun clock).1
    obtain ⟨restCount, post, restBound, restRun, postRelated⟩ :=
      ih (after state instruction) checks.2 guards.2.2 budgets.2 middle middleRelated
    refine ⟨firstCount + restCount, post, Nat.add_le_add firstBound restBound, ?_, postRelated⟩
    intro clock
    rw [show firstCount + restCount + clock = restCount + clock + firstCount by omega,
      firstShift, restRun]

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.checked_trace_evaluator_bounded
