import InitECandidate.Runtime.RlpValidationWitnessRank
import InitECandidate.Runtime.RlpValidationStepBound
import InitECandidate.Runtime.RlpValidationStepControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) rlpValidationStep

/-- The actual original validator loop has a finite input-ranked source-clock
budget, including early failures and the final iteration clearing its flag. -/
theorem evaluate_rlpValidation_loop_bounded {F : Type}
    (frame : BitVec 64) (ceiling inputLimit : Nat)
    (limitBound : inputLimit + 9 < 2^64) (framePositive : 0 < frame.toNat) :
    ∀ (state : PanSemStateFiniteExact 64 F) (valid : RlpValidationLoopWitness state frame ceiling inputLimit),
    valid.rank * 15 ≤ state.clock →
    ∃ result post, evaluateHOLFiniteState state rlpValidationLoop = (result,post) ∧
      state.clock ≤ post.clock + valid.rank * 15 ∧ post.clock ≤ state.clock ∧
      result ≠ some .timeOut ∧ (result = none → post.locals.lookup (ofString "go") = some (.val (.word 0))) := by
  classical
  have visit : ∀ n : Nat, ∀ (state : PanSemStateFiniteExact 64 F)
      (valid : RlpValidationLoopWitness state frame ceiling inputLimit), valid.rank = n → n * 15 ≤ state.clock →
      ∃ result post, evaluateHOLFiniteState state rlpValidationLoop = (result,post) ∧
        state.clock ≤ post.clock + n * 15 ∧ post.clock ≤ state.clock ∧
        result ≠ some .timeOut ∧ (result = none → post.locals.lookup (ofString "go") = some (.val (.word 0))) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro state valid distance budget
      by_cases disabled : valid.flag = 0
      · refine ⟨none,state,?_,by omega,by omega,by simp,?_⟩
        · rw [rlpValidationLoop,evaluateHOLFiniteState_while_total]
          have zero : valid.flag = 0#64 := disabled
          simp [evalHOLFinite,evalHOLExact,valid.flagLocal,zero,Compiler.Encoders.Asm.wordCmpHOL]
        · intro _; simpa [disabled] using valid.flagLocal
      · have positive := valid.rank_bound.1
        have allocation : 15 ≤ n * 15 := by omega
        have nonzero : state.clock ≠ 0 := by omega
        let entry := decClockHOLFinite state
        have entryClock : entry.clock = state.clock - 1 := rfl
        have guard : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
            (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) = some (.val (.word 1)) := by
          have notZero : valid.flag ≠ 0#64 := disabled
          simp [evalHOLFinite,evalHOLExact,valid.flagLocal,notZero,Compiler.Encoders.Asm.wordCmpHOL]
        have bounded := evaluate_rlpValidation_step_bounded entry frame ceiling inputLimit valid.decClock (by omega)
        have control := evaluate_rlpValidation_step_no_loop_control entry
        cases bodyRun : evaluateHOLFiniteState entry rlpValidationStep with
        | mk bodyResult next =>
          rw [bodyRun] at bounded control
          dsimp only at bounded control
          have fixed : ¬entry.clock < next.clock := by omega
          cases bodyResult with
          | none =>
            have unfoldLoop : evaluateHOLFiniteState state rlpValidationLoop = evaluateHOLFiniteState next rlpValidationLoop := by
              rw [rlpValidationLoop,evaluateHOLFiniteState_while_total,guard]
              simp [nonzero,bodyRun,fixClockHOLFinite,fixed,entry]
            have progress := rlpValidation_loop_witness_step entry next frame ceiling inputLimit valid.decClock
              limitBound framePositive (by omega) bodyRun
            rcases progress with cleared | advancing
            · have finished : evaluateHOLFiniteState next rlpValidationLoop = (none,next) := by
                rw [rlpValidationLoop,evaluateHOLFiniteState_while_total]
                simp [evalHOLFinite,evalHOLExact,cleared,Compiler.Encoders.Asm.wordCmpHOL]
              exact ⟨none,next,unfoldLoop.trans finished,by omega,by omega,by simp,by intro _; exact cleared⟩
            · obtain ⟨nextValid,decreases,cost⟩ := advancing
              have smaller : nextValid.rank < n := by
                change rlpValidationRank nextValid.position nextValid.stop nextValid.frames <
                  rlpValidationRank valid.position valid.stop valid.frames at decreases
                unfold RlpValidationLoopWitness.rank at distance ⊢
                omega
              have nextBudget : nextValid.rank * 15 ≤ next.clock := by omega
              obtain ⟨result,post,tail,tailCost,remaining,noTimeout,done⟩ := ih nextValid.rank smaller next nextValid rfl nextBudget
              exact ⟨result,post,unfoldLoop.trans tail,by omega,by omega,noTimeout,done⟩
          | some result =>
            refine ⟨some result,next,?_,by omega,by omega,bounded.2.2,by intro impossible; cases impossible⟩
            rw [rlpValidationLoop,evaluateHOLFiniteState_while_total,guard]
            cases result <;> simp [nonzero,bodyRun,fixClockHOLFinite,fixed,entry] at *
  intro state valid budget
  exact visit valid.rank state valid rfl budget

#print axioms evaluate_rlpValidation_loop_bounded
end InitECandidate.Runtime
