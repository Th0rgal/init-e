import InitECandidate.Runtime.VersionedHashesLoopRank
import InitECandidate.Runtime.VersionedHashesCountFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure VersionedHashesIndexInvariant {F : Type} (state : PanSemStateFiniteExact 64 F) (count : BitVec 64) where
  index : BitVec 64
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  countLocal : state.locals.lookup (ofString "ntx") = some (.val (.word count))
  within : index.toNat ≤ count.toNat
  small : count.toNat < 2^63

theorem versioned_hashes_index_invariant_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count : BitVec 64) (valid : VersionedHashesIndexInvariant state count)
    (active : 0 < versionedHashesRank count state)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    Nonempty (VersionedHashesIndexInvariant post count) ∧ versionedHashesRank count post < versionedHashesRank count state := by
  have rank : versionedHashesRank count state = count.toNat - valid.index.toNat := by
    simp [versionedHashesRank,valid.indexLocal]
  have inside : valid.index.toNat < count.toNat := by rw [rank] at active; omega
  obtain ⟨advanced,within,decreases⟩ := versioned_hashes_rank_decreases state post valid.index count valid.indexLocal inside run
  exact ⟨⟨⟨valid.index + 1,advanced,(versioned_hashes_step_count_frame state post run).trans valid.countLocal,within,valid.small⟩⟩,decreases⟩

theorem versioned_hashes_index_invariant_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64) (valid : VersionedHashesIndexInvariant state count) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) versionedHashesCondition =
      some (.val (.word (if versionedHashesRank count state = 0 then (0 : BitVec 64) else 1))) :=
  versioned_hashes_rank_guard state valid.index count valid.indexLocal valid.countLocal valid.within valid.small

#print axioms versioned_hashes_index_invariant_step
#print axioms versioned_hashes_index_invariant_guard
end InitECandidate.Runtime
