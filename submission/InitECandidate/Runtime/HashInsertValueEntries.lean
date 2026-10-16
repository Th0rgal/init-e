import InitECandidate.Runtime.HashInsertValueWords
import InitECandidate.Runtime.HashInsertValueReverse
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_value_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      values + slot * 8 ≠ orderPos + index * 8 ∧ values + slot * 8 ≠ table + 24)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (valueReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + index * 8)
    (newSeparate : orderPos + index * 8 ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ index →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + index) ∧
      orderPos + slot * 8 ≠ order + count * 8 ∧
      orderPos + slot * 8 ≠ orderPos + index * 8 ∧ orderPos + slot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧ HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post := by
  obtain ⟨post,run,header,agrees,ticks,words⟩ := evaluate_hashInsert_value_words state capacity used table values value order orderPos count index cell
      tableLocal orderLocal orderPosLocal usedLocal indexLocal valueLocal inside valuesDomain valuesMemory valueDomain
      byteDomain byteMemory empty orderDomain orderPosDomain countDomain countMemory agreement noWrap
      valueCountSeparate valueSeparate separate
      entries distinct byteValuesSeparate bookkeepingValuesSeparate
  obtain ⟨checked,checkedRun,_,_,_,reverse⟩ := evaluate_hashInsert_value_reverse state capacity used table values value order orderPos count index cell
      tableLocal orderLocal orderPosLocal usedLocal indexLocal valueLocal inside valuesDomain valuesMemory valueDomain
      byteDomain byteMemory empty orderDomain orderPosDomain countDomain countMemory agreement noWrap
      valueCountSeparate valueSeparate separate
      reverseEntries valueReverse newSeparate reverseSeparate
  have same := congrArg Prod.snd (run.symm.trans checkedRun)
  change post = checked at same
  exact ⟨post,run,header,agrees,ticks,words,by rw [same]; exact reverse⟩

#print axioms evaluate_hashInsert_value_entries
end InitECandidate.Runtime
