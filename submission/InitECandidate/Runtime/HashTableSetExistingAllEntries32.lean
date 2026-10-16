import InitECandidate.Runtime.HashTableArraysValue32
import InitECandidate.Runtime.HashValueWriteGeometry32
import InitECandidate.Runtime.HashReverseValueGeometry32
import InitECandidate.Runtime.HashReverseWordFrame
import InitECandidate.Runtime.HashOrderWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Existing-key suffix of original set preserves the table invariant. -/
theorem HashTableArraysInvariant32.set_existing_tail_all_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count index value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat) (missing : ProgHOL 64)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (orderEntries : HashOrderEntriesBound order capacity count state) :
    ∃ post, evaluateHOLFiniteState state (hashSetExistingTail missing) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity count post ∧
      HashOrderEntriesBound order capacity count post ∧ post.clock = state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have different : index ≠ capacity := by
    intro same
    rw [same] at inside
    omega
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos count bits
  have run := evaluate_hashSet_existing_tail state table index capacity values value missing different
    tableLocal indexLocal valueLocal (invariant.header_domain state table keys stride capacity used values order orderPos count bits 16 (by decide)) invariant.cell16
    (invariant.header_domain state table keys stride capacity used values order orderPos count bits 40 (by decide)) invariant.cell40 (facts.valueDomain index inside)
  let written := sourceWriteWord state (values + index * 8) value
  have valid : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits written := invariant.write_value state table keys stride capacity used values order orderPos count index value bits inside
  have words := entries.write_value_layout32 state table keys stride capacity used values order orderPos count index value bits invariant inside
  have reverse := reverseEntries.after_word state used orderPos capacity count (values + index * 8) value
    (facts.valueSeparate index inside)
    (invariant.value_reverse_separate state table keys stride capacity used values order orderPos count index bits inside)
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have valueAddress := (hashFind_slot_address values index 8 capacity inside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.valuesAligned (by decide)).1
  change (values + index * 8).toNat = values.toNat + index.toNat * 8 at valueAddress
  have ordered := orderEntries.after_word state order capacity count (values + index * 8) value (by
    intro position bound
    have room := invariant.room
    have orderAddress := (hashFind_slot_address order position 8 capacity (by omega)
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
    change (order + position * 8).toNat = order.toNat + position.toNat * 8 at orderAddress
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    intro same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress,valueAddress] at natural
    omega)
  exact ⟨_,run,valid.after_read written _ table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl,
    words.after_read written _ used values capacity rfl rfl rfl,
    reverse.after_read written _ used orderPos capacity count rfl rfl rfl,
    ordered.after_memory written _ order capacity count rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms HashTableArraysInvariant32.set_existing_tail_all_entries
end InitECandidate.Runtime
