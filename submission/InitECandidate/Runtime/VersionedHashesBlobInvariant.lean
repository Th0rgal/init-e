import InitECandidate.Runtime.VersionedHashesBlobRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure VersionedHashesBlobInvariant {F : Type} (state : PanSemStateFiniteExact 64 F) (count : BitVec 64) where
  index : BitVec 64
  indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index))
  countLocal : state.locals.lookup (ofString "nb") = some (.val (.word count))
  within : index.toNat ≤ count.toNat
  small : count.toNat < 2^63

theorem versioned_hashes_blob_invariant_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count : BitVec 64) (valid : VersionedHashesBlobInvariant state count)
    (active : 0 < versionedHashesBlobRank count state)
    (run : evaluateHOLFiniteState state versionedHashesBlobStep = (none,post)) :
    Nonempty (VersionedHashesBlobInvariant post count) ∧ versionedHashesBlobRank count post < versionedHashesBlobRank count state := by
  have rank : versionedHashesBlobRank count state = count.toNat - valid.index.toNat := by
    simp [versionedHashesBlobRank,valid.indexLocal]
  have inside : valid.index.toNat < count.toNat := by rw [rank] at active; omega
  obtain ⟨advanced,within,decreases⟩ := versioned_hashes_blob_rank_decreases state post valid.index count valid.indexLocal inside run
  exact ⟨⟨⟨valid.index + 1,advanced,(versioned_hashes_blob_step_count_frame state post run).trans valid.countLocal,within,valid.small⟩⟩,decreases⟩

theorem versioned_hashes_blob_invariant_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64) (valid : VersionedHashesBlobInvariant state count) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) versionedHashesBlobCondition =
      some (.val (.word (if versionedHashesBlobRank count state = 0 then (0 : BitVec 64) else 1))) :=
  versioned_hashes_blob_rank_guard state valid.index count valid.indexLocal valid.countLocal valid.within valid.small

#print axioms versioned_hashes_blob_invariant_step
#print axioms versioned_hashes_blob_invariant_guard
end InitECandidate.Runtime
