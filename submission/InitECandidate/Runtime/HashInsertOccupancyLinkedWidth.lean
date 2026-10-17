import InitECandidate.Runtime.HashInsertOccupancyMemory
import InitECandidate.Runtime.HashOrderInsertGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual occupancy/bookkeeping evaluation preserves live order linkage,
with every allocation and store-separation premise derived from the table. -/
theorem evaluate_hashInsert_occupancy_linked_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count index cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (inside : index.toNat < capacity.toNat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell) :
    ∃ post, evaluateHOLFiniteState state (.seq hashInsertOccupancyStore hashInsertCountTail) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.clock = state.clock ∧ HashOrderLinked used order orderPos capacity (count + 1) post := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have separate : table + 24 ≠ panByteAlignHOL (used + index) :=
    Ne.symm ((facts.separate index inside index inside).2.2)
  obtain ⟨post,run,memory,ticks,_,_,domain,endian,_⟩ := evaluate_hashInsert_occupancy_count_memory state
    used table order orderPos count index cell tableLocal orderLocal orderPosLocal usedLocal indexLocal
    (facts.byteDomain index inside) byteMemory facts.orderDomain (facts.orderPosDomain index inside) facts.countDomain facts.countMemory separate
  have written := linked.insert_stores_layout_width state keyLength table keys stride capacity used values order orderPos count index cell bits invariant inside byteMemory
  exact ⟨post,run,ticks,written.after_read _ post used order orderPos capacity (count + 1) memory domain endian⟩

#print axioms evaluate_hashInsert_occupancy_linked_width
end InitECandidate.Runtime
