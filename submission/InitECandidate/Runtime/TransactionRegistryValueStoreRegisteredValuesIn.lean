import InitECandidate.Runtime.TransactionRegistryValueStore
import InitECandidate.Runtime.HashTableValuesInLaterRecord
import InitECandidate.Runtime.JournalSavedValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A fresh value buffer beyond all table allocations also preserves watched
registered values and every saved journal value. -/
theorem TransactionRegistryWorld.four_words_registered_values_in {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (destination a b c d : BitVec 64)
    (bounded : destination.toNat + 32 ≤ 33806089496)
    (afterHeader : ts.toNat + 72 ≤ destination.toNat)
    (outside : ∀ table ∈ tables, ∀ pointer keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits pointer state →
      reverse.toNat + capacity.toNat * 8 ≤ destination.toNat)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state) :
    (∀ other ∈ watched, HashTableValuesIn other targets (journalRecordPost32 state destination a b c d)) ∧
    JournalSavedValuesIn journal count.toNat watched targets (journalRecordPost32 state destination a b c d) := by
  constructor
  · intro other belongs
    obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,logicalReady,_,_⟩ := valid.journalWorld.world.ready other (watchedSubset belongs)
    have ready : HashTableReady (widths other) other keys stride capacity used values order reverse items bits pointer state :=
      logicalReady.after_read _ state (widths other) other keys stride capacity used values order reverse items bits pointer rfl rfl rfl rfl rfl
    exact (registered other belongs).journal_record_after state (widths other) other keys stride capacity used values order reverse items destination a b c d bits ready.live.arrays targets bounded
      (outside other (watchedSubset belongs) pointer keys stride capacity used values order reverse items bits ready)
  · have cap := valid.journalWorld.world.capacity
    have bound := valid.journalWorld.journalBound
    have before := valid.journalBeforeTs
    have frame := journalRecordPost32_prefix_frame state journal destination a b c d count.toNat (by omega) bounded (by omega)
    exact saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact frame index inside offset (by simp at belongs ⊢; omega))

#print axioms TransactionRegistryWorld.four_words_registered_values_in
end InitECandidate.Runtime
