import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.HashInsertLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Constructor allocation addresses discharge insertion's memory environment
once the constructor header and allocated memory domains are established. -/
theorem htabNew_insertion_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity count : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (valuesMemory : state.memory (table + 40) = .word (htabNewValues table keyLength capacity))
    (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state (htabNewUsed table keyLength capacity)))
    (room : count.toNat < capacity.toNat) :
    HashInsertTableMemory capacity (htabNewUsed table keyLength capacity) table
      (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
      (htabNewOrderPos table keyLength capacity) count state := by
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := htabNew_insertion_layout table keyLength capacity keyBound budget
  exact hashInsert_table_memory_from_layout capacity (htabNewUsed table keyLength capacity) table
    (htabNewValues table keyLength capacity) (htabNewOrder table keyLength capacity)
    (htabNewOrderPos table keyLength capacity) count state va ua oa ra hv vu uo orr limit
    domain valuesMemory countMemory agreement room

#print axioms htabNew_insertion_memory
end InitECandidate.Runtime
