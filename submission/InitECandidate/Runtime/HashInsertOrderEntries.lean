import InitECandidate.Runtime.HashOrderEntriesLayout
import InitECandidate.Runtime.HashInsertOccupancyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_order_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used table order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (countMemory : state.memory (table + 24) = .word count)
    (countSeparate : table + 24 ≠ panByteAlignHOL (used + index))
    (capacity : BitVec 64)
    (entries : HashOrderEntriesBound order capacity count state)
    (usedAligned : used.toNat % 8 = 0) (orderAligned : order.toNat % 8 = 0)
    (reverseAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : count.toNat < capacity.toNat) (inside : index.toNat < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state (.seq hashInsertOccupancyStore hashInsertCountTail) =
        (some (.returned (.val (.word 0))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧ post.clock = state.clock := by
  let marked := sourceWriteByte state (used + index) 1 cell
  have occupancy := hashOccupancy_aligned_interval used capacity index usedAligned (by omega) inside
  have markedEntries : HashOrderEntriesBound order capacity count marked := by
    intro position before
    obtain ⟨slot,memory,valid⟩ := entries position before
    have address := (hashFind_slot_address order position 8 capacity (by omega)
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      orderAligned (by decide)).1
    have separate : order + position * 8 ≠ panByteAlignHOL (used + index) := by
      intro same
      have equal := congrArg BitVec.toNat same
      rw [address] at equal
      omega
    exact ⟨slot,(sourceWriteByte_memory_other state (used + index) 1 cell _ separate).trans memory,valid⟩
  have valid := markedEntries.bookkeeping_layout marked table order orderPos capacity count index
    orderAligned reverseAligned headerBefore orderBefore bounded room inside
  obtain ⟨post,run,memory,clock,_⟩ := evaluate_hashInsert_occupancy_count_memory state used table order orderPos count index cell
    tableLocal orderLocal orderPosLocal usedLocal indexLocal byteDomain byteMemory orderDomain orderPosDomain
    countDomain countMemory countSeparate
  exact ⟨post,run,valid.after_memory _ post order capacity (count + 1) memory,clock⟩

#print axioms evaluate_hashInsert_order_entries
end InitECandidate.Runtime
