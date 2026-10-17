import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.HashTableReadyJournal
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Four stores beyond every live array retain each registered layout and its
physical separation, including tables with relocated arrays. -/
theorem rollback_registry_after_later_record {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (record a b c d : BitVec 64)
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (bounded : record.toNat + 32 ≤ 33806089496)
    (outside : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      reverse.toNat + capacity.toNat * 8 ≤ record.toNat) :
    (∀ table ∈ tables, RollbackTableReady widths table (journalRecordPost32 state record a b c d)) ∧
    RollbackPhysicalSeparated widths tables (journalRecordPost32 state record a b c d) := by
  let post := journalRecordPost32 state record a b c d
  have retains : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer post := by
    intro table member pointer keys stride capacity used values order reverse items bits ready
    exact ready.journal_record_other state (widths table) table pointer keys stride capacity used values order reverse items record a b c d bits
      bounded (Or.inr (outside table member pointer keys stride capacity used values order reverse items bits ready))
  constructor
  · intro table member
    obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := family table member
    exact ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,retains table member pointer keys stride capacity used values order reverse items bits ready,small,large⟩
  · apply separated.of_footprint_subset
    intro table member address inside
    obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := family table member
    have updated := retains table member pointer keys stride capacity used values order reverse items bits ready
    exact (ready.rollback_footprint_iff state widths table pointer keys stride capacity used values order reverse items bits address).mpr
      ((updated.rollback_footprint_iff post widths table pointer keys stride capacity used values order reverse items bits address).mp inside)

#print axioms rollback_registry_after_later_record
end InitECandidate.Runtime
