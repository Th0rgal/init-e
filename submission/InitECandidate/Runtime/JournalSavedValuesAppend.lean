import InitECandidate.Runtime.JournalSavedValuesIn
import InitECandidate.Runtime.JournalRecordAppendFrame
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The actual four saved-word stores append a registered value while retaining
all earlier saved-value obligations. The presence test matches restore's branch. -/
theorem JournalSavedValuesIn.record_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (journal count table key present value : BitVec 64) (watched targets : Set (BitVec 64))
    (valid : JournalSavedValuesIn journal count.toNat watched targets state)
    (bounded : journal.toNat + (count.toNat + 1) * 32 ≤ 33806089496)
    (aligned : journal.toNat % 8 = 0)
    (registered : table ∈ watched → present ≠ 0 → value ∈ targets) :
    JournalSavedValuesIn journal (count.toNat + 1) watched targets
      (journalRecordPost32 state (journal + count * 32) table key present value) := by
  have countBound : count.toNat + 1 < 2 ^ 64 := by omega
  have next : (count + (1 : BitVec 64)).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]
    rfl
  obtain ⟨location,_,extent⟩ := journal_record_geometry32 journal count (count + 1) (by rw [next]; omega) (by rw [next]; exact bounded) aligned
  have frame := journalRecordPost32_prefix_frame state journal (journal + count * 32) table key present value count.toNat
    (by omega) (by rw [next] at extent; omega) (by omega)
  obtain ⟨t,_,p,v⟩ := journalRecordPost32_fields state (journal + count * 32) table key present value
  apply valid.append (after := journalRecordPost32 state (journal + count * 32) table key present value)
    (by
      intro index inside offset belongs
      exact frame index inside offset (by simp at belongs ⊢; omega)) table present value
  · simpa using t
  · simpa using p
  · simpa using v
  · exact registered

#print axioms JournalSavedValuesIn.record_stores
end InitECandidate.Runtime
