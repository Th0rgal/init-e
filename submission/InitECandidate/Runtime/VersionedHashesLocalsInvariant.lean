import InitECandidate.Runtime.VersionedHashesIndexInvariant
import InitECandidate.Runtime.VersionedHashesArrayFrames
import InitECandidate.Runtime.VersionedHashesStepCursorWord
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The local-variable part of the outer validation invariant. Heap reserves and
readable transaction slices must be supplied separately by the memory invariant. -/
structure VersionedHashesLocalsInvariant {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh : BitVec 64) extends VersionedHashesIndexInvariant state count where
  cursor : BitVec 64
  cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor))
  arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array))
  vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh))
  code : state.code = originalRuntimeCode

def VersionedHashesLocalsInvariant.decClock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh : BitVec 64) (valid : VersionedHashesLocalsInvariant state count array vh) :
    VersionedHashesLocalsInvariant (decClockHOLFinite state) count array vh :=
  ⟨⟨valid.index,valid.indexLocal,valid.countLocal,valid.within,valid.small⟩,
    valid.cursor,valid.cursorLocal,valid.arrayLocal,valid.vhLocal,valid.code⟩

theorem versioned_hashes_locals_invariant_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count array vh : BitVec 64) (valid : VersionedHashesLocalsInvariant state count array vh)
    (active : 0 < versionedHashesRank count state)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    Nonempty (VersionedHashesLocalsInvariant post count array vh) ∧
      versionedHashesRank count post < versionedHashesRank count state := by
  obtain ⟨⟨next⟩,decreases⟩ := versioned_hashes_index_invariant_step state post count valid.toVersionedHashesIndexInvariant active run
  obtain ⟨cursor,cursorLocal⟩ := versioned_hashes_step_cursor_word state post valid.cursor valid.cursorLocal run
  have metadata := evaluateHOLFiniteState_metadata state versionedHashesStep
  rw [run] at metadata
  exact ⟨⟨⟨next,cursor,cursorLocal,(versioned_hashes_step_array_frame state post run).trans valid.arrayLocal,
    (versioned_hashes_step_vh_frame state post run).trans valid.vhLocal,metadata.1.trans valid.code⟩⟩,decreases⟩

#print axioms VersionedHashesLocalsInvariant.decClock
#print axioms versioned_hashes_locals_invariant_step
end InitECandidate.Runtime
