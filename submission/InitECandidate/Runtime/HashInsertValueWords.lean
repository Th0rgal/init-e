import InitECandidate.Runtime.HashInsertValueTail
import InitECandidate.Runtime.HashInsertCountWords
import InitECandidate.Runtime.HashValueWordStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_value_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (valuesDomain : state.memaddrs (table + 40)) (valuesMemory : state.memory (table + 40) = .word values)
    (valueDomain : state.memaddrs (values + index * 8))
    (byteDomain : state.memaddrs (panByteAlignHOL (used + index)))
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24)) (countMemory : state.memory (table + 24) = .word count)
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (noWrap : count.toNat + 1 < 2 ^ 64)
    (valueCountSeparate : table + 24 ≠ values + index * 8)
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ values + index * 8)
    (separate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧ panByteAlignHOL (used + slot) ≠ table + 24)
    (entries : HashValueEntriesWord used values capacity state)
    (distinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ index →
      values + slot * 8 ≠ values + index * 8)
    (byteValuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ panByteAlignHOL (used + index))
    (bookkeepingValuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + count * 8 ∧
      values + slot * 8 ≠ orderPos + index * 8 ∧ values + slot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧ HashValueEntriesWord used values capacity post := by
  have d40 : state.memaddrs (table + 40#64) := valuesDomain
  have c40 : state.memory (table + 40#64) = .word values := valuesMemory
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetValueAddress =
      some (.val (.word (values + index * 8))) := by
    simp [hashSetValueAddress,evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40]
  have store := evaluate_store_word state (values + index * 8) value hashSetValueAddress (.var .local (ofString "value"))
    address valueLocal valueDomain
  let written := sourceWriteWord state (values + index * 8) value
  have literalSeparate : panByteAlignHOL (used + index) ≠ values + index * 8#64 := valueSeparate index inside
  have literalCountSeparate : table + 24#64 ≠ values + index * 8#64 := valueCountSeparate
  have byteAfter : written.memory (panByteAlignHOL (used + index)) = .word cell := by
    simpa [written,sourceWriteWord,literalSeparate] using byteMemory
  have emptyAfter : hashOccupancyRead written used index = some 0 := by
    have same : hashOccupancyRead written used index = hashOccupancyRead state used index := by
      simp [hashOccupancyRead,written,panMemLoadByteHOL,sourceWriteWord,literalSeparate]
      rfl
    exact same.trans empty
  have countAfter : written.memory (table + 24) = .word count := by
    simpa [written,sourceWriteWord,literalCountSeparate] using countMemory
  have agreementAfter : count.toNat = hashOccupiedCount capacity (hashOccupancyRead written used) := by
    rw [sourceWriteWord_occupancy_preserved state capacity used (values + index * 8) value valueSeparate]
    exact agreement
  have writtenEntries := entries.write_value state used values capacity index value valueSeparate distinct
  have writtenValue : written.memory (values + index * 8) = .word value := by
    simp only [written,sourceWriteWord,ite_true]
  obtain ⟨post,tail,header,agrees,ticks,postEntries⟩ := evaluate_hashInsert_count_words written capacity used table order orderPos count index cell values value
    tableLocal orderLocal orderPosLocal usedLocal indexLocal inside byteDomain byteAfter emptyAfter orderDomain orderPosDomain
    countDomain countAfter agreementAfter noWrap separate writtenEntries writtenValue byteValuesSeparate bookkeepingValuesSeparate
  refine ⟨post,?_,header,agrees,ticks,postEntries⟩
  unfold hashInsertValueTail
  rw [evaluateHOLFiniteState_seq_line780,store]
  exact tail

#print axioms evaluate_hashInsert_value_words
end InitECandidate.Runtime
