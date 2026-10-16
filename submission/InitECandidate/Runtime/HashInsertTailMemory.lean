import InitECandidate.Runtime.HashInsertTailReady
import InitECandidate.Runtime.HashInsertValueMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashInsertTailReady.run_memory {F : Type}
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (state : PanSemStateFiniteExact 64 F)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, watched ≠ values + index * 8 → watched ≠ panByteAlignHOL (used + index) →
        watched ≠ order + count * 8 → watched ≠ orderPos + index * 8 → watched ≠ table + 24 →
        post.memory watched = state.memory watched := by
  exact evaluate_hashInsert_value_tail_memory state capacity used table values value order orderPos count index cell
    ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.valueLocal ready.inside ready.valuesDomain ready.valuesMemory ready.valueDomain ready.byteDomain ready.byteMemory ready.empty ready.orderDomain ready.orderPosDomain ready.countDomain ready.countMemory ready.agreement ready.noWrap ready.valueCountSeparate ready.valueSeparate ready.separate

#print axioms HashInsertTailReady.run_memory
end InitECandidate.Runtime
