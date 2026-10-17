import InitECandidate.Runtime.RollbackRegistryStores
import InitECandidate.Runtime.HashTableReadyJournal32
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Saving a journal record below every registered header preserves the entire
mixed-width table registry and physical separation through all four stores. -/
theorem rollback_registry_after_record {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (record table key present value : BitVec 64)
    (family : ∀ other ∈ tables, RollbackTableReady widths other state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (bounded : record.toNat + 32 ≤ 33806089496)
    (headers : ∀ other ∈ tables, record.toNat + 32 ≤ other.toNat) :
    (∀ other ∈ tables, RollbackTableReady widths other (journalRecordPost32 state record table key present value)) ∧
    RollbackPhysicalSeparated widths tables (journalRecordPost32 state record table key present value) := by
  have before : ∀ offset : Nat, offset < 32 → ∀ other ∈ tables, (record + BitVec.ofNat 64 offset).toNat < other.toNat := by
    intro offset small other member
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    have header := headers other member
    omega
  have outside : ∀ (current : PanSemStateFiniteExact 64 F) (offset : Nat), offset < 32 →
      ∀ other ∈ tables, ¬rollbackTableFootprint widths other current (record + BitVec.ofNat 64 offset) := by
    intro current offset small other member inside
    have lower := rollback_footprint_above_header inside
    have upper := before offset small other member
    omega
  obtain ⟨one,sepOne⟩ := rollback_registry_after_word state widths tables record table family separated (by simpa using outside state 0 (by decide))
  obtain ⟨two,sepTwo⟩ := rollback_registry_after_word (sourceWriteWord state record table) widths tables (record + 8) key one sepOne (outside _ 8 (by decide))
  obtain ⟨three,sepThree⟩ := rollback_registry_after_word (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) widths tables (record + 16) present two sepTwo (outside _ 16 (by decide))
  exact rollback_registry_after_word (sourceWriteWord (sourceWriteWord (sourceWriteWord state record table) (record + 8) key) (record + 16) present) widths tables (record + 24) value three sepThree (outside _ 24 (by decide))

#print axioms rollback_registry_after_record
end InitECandidate.Runtime
