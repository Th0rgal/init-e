import InitECandidate.Runtime.VersionedHashesRuntimeLoopBound
import InitECandidate.Runtime.VersionedHashesGuardedRuntimeInvariantStep
import InitECandidate.Runtime.VersionedHashesGuardedRuntimeInvariantStepBound
import InitECandidate.Runtime.VersionedHashesUniformSourceStepBound
import InitECandidate.Runtime.VersionedHashesStepControl
import InitECandidate.Runtime.RankedLoopReturnsInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete original transaction loop is bounded, including early hash
mismatch returns, decoder exceptions, and inaccessible-memory failures. -/
theorem evaluate_versioned_hashes_guarded_runtime_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : VersionedHashesGuardedRuntimeInvariant state count array vh input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (arrayAbove : ceiling ≤ array.toNat)
    (countLimit : inputLimit * 120 < 2^64)
    (budget : versionedHashesRank count state * (versionedHashesTransactionStepCost inputLength.toNat + 1) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state versionedHashesLoop = (result,post) ∧
      state.clock ≤ post.clock + versionedHashesRank count state * (versionedHashesTransactionStepCost inputLength.toNat + 1) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → Nonempty (VersionedHashesGuardedRuntimeInvariant post count array vh input inputLength scratch frame ceiling) ∧
        versionedHashesRank count post = 0) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (VersionedHashesGuardedRuntimeInvariant current count array vh input inputLength scratch frame ceiling)
  let cost := versionedHashesTransactionStepCost inputLength.toNat
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address)) versionedHashesCondition =
      some (.val (.word (if versionedHashesRank count current = 0 then 0 else 1))) := by
    rintro current ⟨witness⟩
    exact versioned_hashes_index_invariant_guard current count witness.locals.toVersionedHashesIndexInvariant
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness⟩
    exact ⟨witness.decClock current count array vh input inputLength scratch frame ceiling⟩
  have step : ∀ current, invariant current → 0 < versionedHashesRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current versionedHashesStep = (none,post) ∧ invariant post ∧
          versionedHashesRank count post < versionedHashesRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current versionedHashesStep = (some result,post))) := by
    rintro current ⟨witness⟩ positive ticks
    have bounded := versioned_hashes_guarded_runtime_invariant_step_bounded current
      count array vh input inputLength scratch frame ceiling inputLimit witness inputBound limitBound
      orderedFrame framePositive scratchBelow inputBeforeFrame countLimit positive ticks
    have control := versioned_hashes_step_no_loop_control current
    cases run : evaluateHOLFiniteState current versionedHashesStep with
    | mk result post =>
      rw [run] at bounded control
      dsimp only at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := versioned_hashes_guarded_runtime_invariant_step current post count array vh input inputLength scratch frame ceiling inputLimit
          witness inputBound limitBound orderedFrame framePositive scratchBelow inputBeforeFrame arrayAbove countLimit positive
          ((Nat.le_add_right _ (1 + versionedHashesScanCost)).trans ticks) run
        exact Or.inl ⟨rfl,next,decreases⟩
      | some result =>
        exact Or.inr ⟨result,(fun equal => control.2 (congrArg some equal)),
          (fun equal => bounded.2.2 (congrArg some equal)),(fun equal => control.1 (congrArg some equal)),rfl⟩
  rw [source_versioned_hashes_loop]
  exact evaluate_ranked_loop_returns_invariant versionedHashesCondition versionedHashesStep invariant
    (versionedHashesRank count) cost guard enter (fun current => rfl) step state ⟨valid⟩ budget

#print axioms evaluate_versioned_hashes_guarded_runtime_loop_bounded
end InitECandidate.Runtime
