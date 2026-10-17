import InitECandidate.Runtime.TypedJournalUndoAppend
import InitECandidate.Runtime.JournalRecordAppendFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The four actual record stores append a typed undo record, framing the
entire live prefix and retaining the saved key's table-specific extent. -/
theorem TypedJournalUndoRecords.after_record {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64)
    (journal table key present value : BitVec 64) (count : Nat)
    (valid : TypedJournalUndoRecords widths journal count state)
    (bounded : journal.toNat + count * 32 ≤ 33806089496)
    (recordBound : (journal + BitVec.ofNat 64 count * 32).toNat + 32 ≤ 33806089496)
    (afterPrefix : journal.toNat + count * 32 ≤ (journal + BitVec.ofNat 64 count * 32).toNat)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (fields : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + BitVec.ofNat 64 count * 32 + BitVec.ofNat 64 offset))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    TypedJournalUndoRecords widths journal (count + 1)
      (journalRecordPost32 state (journal + BitVec.ofNat 64 count * 32) table key present value) := by
  obtain ⟨tableCell,keyCell,presentCell,valueCell⟩ := journalRecordPost32_fields state (journal + BitVec.ofNat 64 count * 32) table key present value
  exact valid.append rfl
    (journalRecordPost32_prefix_frame state journal (journal + BitVec.ofNat 64 count * 32) table key present value count bounded recordBound afterPrefix)
    table key present value supported tableCell keyCell presentCell valueCell fields aligned words bytes

#print axioms TypedJournalUndoRecords.after_record
end InitECandidate.Runtime
