import InitECandidate.Runtime.JournalUndoRecords
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem JournalUndoRecords.after_read {F : Type} (before after : PanSemStateFiniteExact 64 F)
    (journal : BitVec 64) (count : Nat) (valid : JournalUndoRecords journal count before)
    (memory : after.memory = before.memory) (domain : after.memaddrs = before.memaddrs) :
    JournalUndoRecords journal count after := by
  apply valid.after_frame (after := after) (Nat.le_refl _) domain
  intro index inside offset member
  rw [memory]

#print axioms JournalUndoRecords.after_read
end InitECandidate.Runtime
