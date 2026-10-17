import InitECandidate.Runtime.HashNewHeader
import InitECandidate.Runtime.HashTableReadyJournalOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Constructor scalar-header stores preserve an earlier ready table. -/
theorem HashTableReady32.new_header_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items newTable keyLength newStride newCapacity : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (bounded : newTable.toNat + 32 ≤ 33806089496)
    (outside : newTable.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ newTable.toNat) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (htabNewHeaderPost state newTable keyLength newStride newCapacity) := by
  simpa [htabNewHeaderPost,journalRecordPost32] using
    ready.journal_record_other state table pointer keys stride capacity used values order orderPos items newTable keyLength newStride newCapacity 0 bits bounded outside

#print axioms HashTableReady32.new_header_other
end InitECandidate.Runtime
