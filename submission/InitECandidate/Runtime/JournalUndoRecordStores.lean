import InitECandidate.Runtime.JournalUndoRecords
import InitECandidate.Runtime.HashDeleteFinalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An actual source word write leaves every disjoint live undo field intact. -/
theorem JournalUndoRecords.after_word {F : Type} {journal : BitVec 64} {count : Nat}
    (state : PanSemStateFiniteExact 64 F) (address value : BitVec 64)
    (valid : JournalUndoRecords journal count state)
    (outside : ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset ≠ address) :
    JournalUndoRecords journal count (sourceWriteWord state address value) := by
  apply valid.after_frame (after := sourceWriteWord state address value) (Nat.le_refl _) rfl
  intro index inside offset member
  have different := outside index inside offset member
  simp only [sourceWriteWord]
  simp
  intro equal
  exact False.elim (different equal)

/-- Byte stores affect their aligned containing word, not just the byte address. -/
theorem JournalUndoRecords.after_byte {F : Type} {journal : BitVec 64} {count : Nat}
    (state : PanSemStateFiniteExact 64 F) (address value cell : BitVec 64)
    (valid : JournalUndoRecords journal count state)
    (outside : ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset ≠ panByteAlignHOL address) :
    JournalUndoRecords journal count (sourceWriteByte state address value cell) := by
  exact valid.after_word state (panByteAlignHOL address) _ outside

/-- Apply the frame to the exact occupancy clear used by original deletion. -/
theorem evaluate_hashDelete_clear_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal base hole cell : BitVec 64) (count : Nat)
    (valid : JournalUndoRecords journal count state)
    (usedLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "used") = some (.val (.word base)))
    (holeLocal : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "i") = some (.val (.word hole)))
    (domain : state.memaddrs (panByteAlignHOL (base + hole)))
    (memory : state.memory (panByteAlignHOL (base + hole)) = .word cell)
    (outside : ∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
      journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset ≠ panByteAlignHOL (base + hole)) :
    ∃ post, evaluateHOLFiniteState state hashDeleteClear = (none,post) ∧ JournalUndoRecords journal count post := by
  exact ⟨sourceWriteByte state (base + hole) 0 cell,
    (evaluate_hashDelete_clear state base hole cell usedLocal holeLocal domain memory).1,
    valid.after_byte state (base + hole) 0 cell outside⟩

#print axioms JournalUndoRecords.after_word
#print axioms JournalUndoRecords.after_byte
#print axioms evaluate_hashDelete_clear_journal
end InitECandidate.Runtime
