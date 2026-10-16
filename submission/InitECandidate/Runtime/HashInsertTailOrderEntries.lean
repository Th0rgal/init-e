import InitECandidate.Runtime.HashInsertValueOrderEntries
import InitECandidate.Runtime.HashInsertTailReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The insertion-ready memory facts support order validity as well as count
agreement for the actual post-copy source suffix. -/
theorem HashInsertTailReady.run_order_entries {F : Type}
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (entries : HashOrderEntriesBound order capacity count state)
    (valuesAligned : values.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : count.toNat < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock := by
  exact evaluate_hashInsert_value_order_entries state capacity used table values value order orderPos count index cell
    ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.valueLocal ready.inside
    ready.valuesDomain ready.valuesMemory ready.valueDomain ready.byteDomain ready.byteMemory ready.empty ready.orderDomain
    ready.orderPosDomain ready.countDomain ready.countMemory ready.agreement ready.noWrap ready.valueCountSeparate
    ready.valueSeparate ready.separate entries valuesAligned usedAligned orderAligned reverseAligned headerBefore
    valuesBefore usedBefore orderBefore bounded room

#print axioms HashInsertTailReady.run_order_entries
end InitECandidate.Runtime
