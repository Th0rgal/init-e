import InitECandidate.Runtime.HashTableArraysMemory
import InitECandidate.Runtime.HashInsertValueEntries
import InitECandidate.Runtime.HashValueInsertGeometryWidth
import InitECandidate.Runtime.HashReverseInsertGeometryWidth
import InitECandidate.Runtime.HashReverseValueGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual value-write, occupancy-mark, and bookkeeping suffix preserves
both entry invariants using the table layout for all address obligations. -/
theorem HashTableArraysInvariant.insert_value_entries_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values value order orderPos count index cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧ HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  obtain ⟨distinct,byteValues,bookkeeping⟩ := invariant.insert_value_separation_width state keyLength table keys stride capacity used values order orderPos count index bits inside
  obtain ⟨newSeparate,reverseSeparate⟩ := invariant.insert_reverse_separation_width state keyLength table keys stride capacity used values order orderPos count index bits inside
  exact evaluate_hashInsert_value_entries state capacity used table values value order orderPos count index cell
    tableLocal orderLocal orderPosLocal usedLocal indexLocal valueLocal inside
    facts.valuesDomain facts.valuesMemory (facts.valueDomain index inside)
    (facts.byteDomain index inside) byteMemory empty facts.orderDomain (facts.orderPosDomain index inside)
    facts.countDomain facts.countMemory facts.agreement facts.noWrap
    (facts.valueCountSeparate index inside) (facts.valueSeparate index inside) (facts.separate index inside)
    entries distinct byteValues bookkeeping reverseEntries
    (invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos count index bits inside)
    newSeparate reverseSeparate

#print axioms HashTableArraysInvariant.insert_value_entries_width
end InitECandidate.Runtime
