import InitECandidate.Runtime.HashInsertCountInvariant
import InitECandidate.Runtime.HashInsertCountTailFrame
import InitECandidate.Runtime.HashReverseInsertStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_count_reverse {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat < capacity.toNat)
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (noWrap : count.toNat + 1 < 2 ^ 64)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧
      panByteAlignHOL (used + slot) ≠ table + 24)
    (entries : HashReverseEntriesBound used orderPos capacity count state)
    (newSeparate : orderPos + index * 8 ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ index →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + index) ∧
      orderPos + slot * 8 ≠ order + count * 8 ∧
      orderPos + slot * 8 ≠ orderPos + index * 8 ∧ orderPos + slot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state (.seq hashInsertOccupancyStore hashInsertCountTail) =
        (some (.returned (.val (.word 0))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post := by
  let marked := sourceWriteByte state (used + index) 1 cell
  have store : evaluateHOLFiniteState state hashInsertOccupancyStore = (none,marked) := by
    apply evaluate_source_storeByte
    · simp [evalHOLExact,evalListHOLExact,usedLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · rfl
    · exact byteDomain
    · exact byteMemory
  have headerAfter : marked.memory (table + 24) = .word count := by
    exact (sourceWriteByte_memory_other state (used + index) 1 cell (table + 24)
      (Ne.symm (separate index inside).2.2)).trans countMemory
  obtain ⟨post,tail,header,clock,memory,addresses,endian,preserved⟩ := evaluate_hashInsert_count_tail_frame marked
    table order orderPos count index tableLocal orderLocal orderPosLocal indexLocal
    orderDomain orderPosDomain countDomain headerAfter
  have countAfter := preserved capacity used separate
  have filled := sourceWriteByte_occupancy_fill state capacity used index cell inside byteDomain byteMemory empty
  have countWord : (count + 1).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by exact noWrap)]
    rfl
  have valid := entries.insert_stores state used order orderPos capacity count index table cell noWrap byteMemory
    newSeparate separate reverseSeparate
  refine ⟨post,evaluate_seq_none store tail,header,?_,clock,
    valid.after_read _ post used orderPos capacity (count + 1) memory addresses endian⟩
  rw [countAfter,filled,← agreement,countWord]

#print axioms evaluate_hashInsert_count_reverse
end InitECandidate.Runtime
