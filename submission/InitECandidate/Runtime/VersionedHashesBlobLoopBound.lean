import InitECandidate.Runtime.VersionedHashesBlobLocals
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.NoLoopControlStores
import InitECandidate.Runtime.RankedLoopReturnsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_blob_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count tx vh : BitVec 64) (valid : VersionedHashesBlobLoopWitness state count tx vh)
    (active : 0 < versionedHashesBlobRank count state)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    Nonempty (VersionedHashesBlobLoopWitness post count tx vh) ∧
      versionedHashesBlobRank count post < versionedHashesBlobRank count state := by
  obtain ⟨⟨next⟩,decreases⟩ := versioned_hashes_blob_invariant_step state post count valid.toVersionedHashesBlobInvariant active run
  obtain ⟨txLocal,vhLocal,kLocal⟩ := versioned_hashes_blob_typed_locals_step state post count tx vh valid run
  have metadata := evaluateHOLFiniteState_metadata state versionedHashesBlobStep
  rw [run] at metadata
  exact ⟨⟨⟨next,valid.cursor + 1,kLocal,txLocal,vhLocal,metadata.1.trans valid.code⟩⟩,decreases⟩

/-- Each original comparison costs at most129 ticks plus the loop-entry tick.
Errors and early returns terminate within the same bound. -/
theorem evaluate_versioned_hashes_blob_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh : BitVec 64) (valid : VersionedHashesBlobLoopWitness state count tx vh)
    (budget : versionedHashesBlobRank count state * 130 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state versionedHashesBlobLoop = (result,post) ∧
      state.clock ≤ post.clock + versionedHashesBlobRank count state * 130 ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → Nonempty (VersionedHashesBlobLoopWitness post count tx vh) ∧ versionedHashesBlobRank count post = 0) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => Nonempty (VersionedHashesBlobLoopWitness current count tx vh)
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness⟩
    exact ⟨⟨⟨witness.index,witness.indexLocal,witness.countLocal,witness.within,witness.small⟩,
      witness.cursor,witness.cursorLocal,witness.txLocal,witness.vhLocal,witness.code⟩⟩
  have step : ∀ current, invariant current → 0 < versionedHashesBlobRank count current → 129 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 129 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current versionedHashesBlobStep = (none,post) ∧ invariant post ∧
          versionedHashesBlobRank count post < versionedHashesBlobRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current versionedHashesBlobStep = (some result,post))) := by
    rintro current ⟨witness⟩ active ticks
    have bounded := versioned_hashes_blob_witness_step_bounded current count tx vh witness ticks
    have control := evaluate_noLoopControlStores versionedHashesBlobStep
      (by rw [source_versioned_hashes_blob_step]; rfl) current
    cases run : evaluateHOLFiniteState current versionedHashesBlobStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := versioned_hashes_blob_witness_step current post count tx vh witness active run
        exact Or.inl ⟨rfl,next,decreases⟩
      | some result =>
        exact Or.inr ⟨result,(by intro eq; subst result; exact control.2 rfl),
          (by intro eq; subst result; exact bounded.2.2 rfl),
          (by intro eq; subst result; exact control.1 rfl),rfl⟩
  obtain ⟨result,post,run,total,remaining,noTimeout,done⟩ := evaluate_ranked_loop_returns_invariant
    versionedHashesBlobCondition versionedHashesBlobStep invariant (versionedHashesBlobRank count) 129
    (by rintro current ⟨witness⟩; exact versioned_hashes_blob_invariant_guard current count witness.toVersionedHashesBlobInvariant)
    enter (by intro current; rfl) step state ⟨valid⟩ budget
  exact ⟨result,post,(by rw [source_versioned_hashes_blob_loop]; exact run),total,remaining,noTimeout,done⟩

#print axioms versioned_hashes_blob_witness_step
#print axioms evaluate_versioned_hashes_blob_loop_bounded
end InitECandidate.Runtime
