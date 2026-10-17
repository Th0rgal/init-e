import InitECandidate.Runtime.HashTableValuesInMutation
import InitECandidate.Runtime.HashTableSetExistingPhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Writing a registered pointer into the actual value array retains pointer
membership, using the table's established separation and slot geometry. -/
theorem HashTableValuesIn.write_value_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count changed value : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (member : value ∈ targets) (inside : changed.toNat < capacity.toNat) :
    HashTableValuesIn table targets (sourceWriteWord state (values + changed * 8) value) := by
  have updated := arrays.write_value_width state keyLength table keys stride capacity used values order orderPos count changed value bits inside
  have facts := arrays.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have address : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
    intro slot bound
    exact (hashFind_slot_address values slot 8 capacity bound
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) arrays.valuesAligned (by decide)).1
  apply entries.write_slot state _ table capacity used values changed value targets member
    arrays.cell16 arrays.cell48 arrays.cell40 updated.cell16 updated.cell48 updated.cell40
  · simp [sourceWriteWord]
  · intro slot bound _
    have separate : panByteAlignHOL (used + slot) ≠ values + changed * 8#64 := facts.valueSeparate changed inside slot bound
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,separate]
    rfl
  · intro slot bound different
    have separate : values + slot * 8 ≠ values + changed * 8 := by
      intro same
      have equal := congrArg BitVec.toNat same
      rw [address slot bound,address changed inside] at equal
      apply different
      apply BitVec.eq_of_toNat_eq
      omega
    change (if values + slot * 8 = values + changed * 8 then HolWordLab.word value else _) = _
    rw [if_neg separate]

/-- The original existing-key update returns normally, retaining both the full
table invariant and membership of every occupied value in the target registry. -/
theorem HashTableReady.set_existing_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat) (missing : ProgHOL 64) :
    ∃ post, evaluateHOLFiniteState state (hashSetExistingTail missing) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      HashTableValuesIn table targets post ∧ post.clock = state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,_,clock,globals,code,domain,endian⟩ :=
    ready.set_existing_with_physical_frame state keyLength table pointer keys stride capacity used values order orderPos items index value bits
      tableLocal indexLocal valueLocal inside missing
  have facts := ready.live.arrays.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  have checked := evaluate_hashSet_existing_tail state table index capacity values value missing
    (by intro equal; rw [equal] at inside; omega) tableLocal indexLocal valueLocal
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) ready.live.arrays.cell16
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 40 (by decide)) ready.live.arrays.cell40
    (facts.valueDomain index inside)
  have same : post = emptyLocalsHOLFinite (sourceWriteWord state (values + index * 8) value) := congrArg Prod.snd (run.symm.trans checked)
  have written := entries.write_value_layout state keyLength table keys stride capacity used values order orderPos items index value bits
    ready.live.arrays targets member inside
  refine ⟨post,run,valid,?_,clock,globals,code,domain,endian⟩
  rw [same]
  exact written.after_read rfl rfl rfl

#print axioms HashTableValuesIn.write_value_layout
#print axioms HashTableReady.set_existing_values_in
end InitECandidate.Runtime
