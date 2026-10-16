import InitECandidate.Runtime.HashInsertCountTail
import InitECandidate.Runtime.HashValueInsertBookkeeping
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_count_value_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table order orderPos count index used values capacity : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (countLocal : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (orderDomain : state.memaddrs (order + count * 8))
    (orderPosDomain : state.memaddrs (orderPos + index * 8))
    (countDomain : state.memaddrs (table + 24))
    (entries : HashValueEntriesWord used values capacity state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + count * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + index * 8 ∧
      panByteAlignHOL (used + slot) ≠ table + 24)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + count * 8 ∧
      values + slot * 8 ≠ orderPos + index * 8 ∧
      values + slot * 8 ≠ table + 24) :
    ∃ post, evaluateHOLFiniteState state hashInsertCountStores = (some (.returned (.val (.word 0))),post) ∧
      HashValueEntriesWord used values capacity post ∧ post.clock = state.clock := by
  have run := evaluate_hashInsert_count_stores state table order orderPos count index
    tableLocal orderLocal orderPosLocal countLocal indexLocal orderDomain orderPosDomain countDomain
  have valid := entries.insert_bookkeeping state used values capacity table order orderPos count index
    occupancySeparate valuesSeparate
  rw [run]
  exact ⟨_,rfl,valid.after_read _ _ used values capacity rfl rfl rfl,rfl⟩

#print axioms evaluate_hashInsert_count_value_words
end InitECandidate.Runtime
