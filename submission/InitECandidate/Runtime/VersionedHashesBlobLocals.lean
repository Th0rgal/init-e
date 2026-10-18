import InitECandidate.Runtime.VersionedHashesBlobInvariant
import InitECandidate.Runtime.VersionedHashesBlobStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_blob_step_tx_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    post.locals.lookup (ofString "tx") = state.locals.lookup (ofString "tx") := by
  apply evaluate_normalLocalFrame (ofString "tx") versionedHashesBlobStep _ state post run
  rw [source_versioned_hashes_blob_step]
  rfl

theorem versioned_hashes_blob_step_vh_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    post.locals.lookup (ofString "vh") = state.locals.lookup (ofString "vh") := by
  apply evaluate_normalLocalFrame (ofString "vh") versionedHashesBlobStep _ state post run
  rw [source_versioned_hashes_blob_step]
  rfl

/-- A normal comparison advances the shared versioned-hash cursor as well as j. -/
theorem versioned_hashes_blob_step_k_adds_one : NormalLocalAdd (ofString "k") 1 versionedHashesBlobStep := by
  rw [source_versioned_hashes_blob_step]
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    exact evaluate_normalLocalFrame (ofString "k") versionedHashesBlobGuard (by rfl) state post run
  · apply normalLocalAdd_decCall _ _ _ _ _ _ _ (by decide)
    unfold versionedHashesCompareTail
    apply normalLocalAdd_seq_normal_frame
    · intro F state post run
      exact evaluate_normalLocalFrame (ofString "k") _ (by rfl) state post run
    · intro F state post index binding run
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases firstRun : evaluateHOLFiniteState state (.assign .local (ofString "k")
          (.op .add [.var .local (ofString "k"),.const 1])) with
      | mk result middle =>
        rw [firstRun] at run
        cases result with
        | none =>
          have advanced := normalLocalAdd_assign (ofString "k") 1 state middle index binding firstRun
          have kept := evaluate_normalLocalFrame (ofString "k")
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) (by rfl) middle post run
          exact kept.trans advanced
        | some result => cases run

structure VersionedHashesBlobLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh : BitVec 64) extends VersionedHashesBlobInvariant state count where
  cursor : BitVec 64
  cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor))
  txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx))
  vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh))
  code : state.code = originalRuntimeCode

/-- Normal comparison preserves every typed local needed by the next cost bound.
The cursor addition may wrap; termination uses the separately bounded j cursor. -/
theorem versioned_hashes_blob_typed_locals_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count tx vh : BitVec 64) (valid : VersionedHashesBlobLoopWitness state count tx vh)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    post.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
    post.locals.lookup (ofString "vh") = some (.val (.word vh)) ∧
    post.locals.lookup (ofString "k") = some (.val (.word (valid.cursor + 1))) := by
  exact ⟨(versioned_hashes_blob_step_tx_frame state post run).trans valid.txLocal,
    (versioned_hashes_blob_step_vh_frame state post run).trans valid.vhLocal,
    versioned_hashes_blob_step_k_adds_one state post valid.cursor valid.cursorLocal run⟩

theorem versioned_hashes_blob_witness_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh : BitVec 64) (valid : VersionedHashesBlobLoopWitness state count tx vh)
    (budget : 129 ≤ state.clock) :
    let output := evaluateHOLFiniteState state versionedHashesBlobStep
    state.clock ≤ output.2.clock + 129 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut :=
  versioned_hashes_blob_step_typed_bounded state tx valid.index vh valid.cursor
    valid.txLocal valid.indexLocal valid.vhLocal valid.cursorLocal valid.code budget

#print axioms versioned_hashes_blob_typed_locals_step
#print axioms versioned_hashes_blob_witness_step_bounded
#print axioms versioned_hashes_blob_step_tx_frame
#print axioms versioned_hashes_blob_step_vh_frame
#print axioms versioned_hashes_blob_step_k_adds_one
end InitECandidate.Runtime
