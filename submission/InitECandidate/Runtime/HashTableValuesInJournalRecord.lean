import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
import InitECandidate.Runtime.JournalRecordSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Saving a journal record below a table cannot change its registered values. -/
theorem HashTableValuesIn.journal_record_before {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count record savedTable savedKey present savedValue : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (before : record.toNat + 32 ≤ table.toNat) :
    HashTableValuesIn table targets (journalRecordPost32 state record savedTable savedKey present savedValue) := by
  have hv := arrays.headerValues
  have hk := arrays.headerKeys
  have ku := arrays.keysBefore
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have separate (offset : Nat) (small : offset < 32) :
      ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order orderPos address →
        address ≠ record + BitVec.ofNat 64 offset := by
    intro address inside same
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have location : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    rw [same] at inside
    unfold tablePhysicalRegion at inside
    omega
  apply entries.physical_frame state _ keyLength table keys stride capacity used values order orderPos count bits arrays targets
  · intro address inside
    have zero : address ≠ record := by simpa using separate 0 (by decide) address inside
    have eight : address ≠ record + (8 : BitVec 64) := separate 8 (by decide) address inside
    have sixteen : address ≠ record + (16 : BitVec 64) := separate 16 (by decide) address inside
    have twentyFour : address ≠ record + (24 : BitVec 64) := separate 24 (by decide) address inside
    simp only [journalRecordPost32,sourceWriteWord,if_neg zero,if_neg eight,if_neg sixteen,if_neg twentyFour]
  · rfl
  · rfl

/-- The original jset record stores transmit registered values to their actual
continuation state, with no restriction on the old value being journaled. -/
theorem evaluate_journalRecordSource_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count record savedTable savedKey present savedValue : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (before : record.toNat + 32 ≤ table.toNat)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word savedTable)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word savedValue)]))
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (record + BitVec.ofNat 64 offset)) :
    ∃ post : PanSemStateFiniteExact 64 F,
      (∀ continuation, evaluateHOLFiniteState state (journalRecordSource32 continuation) = evaluateHOLFiniteState post continuation) ∧
      HashTableValuesIn table targets post ∧ post.clock = state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  exact ⟨journalRecordPost32 state record savedTable savedKey present savedValue,
    (fun continuation => evaluate_journalRecordSource32 state record savedTable savedKey present savedValue continuation r t kc old domain),
    entries.journal_record_before state keyLength table keys stride capacity used values order orderPos count record savedTable savedKey present savedValue bits arrays targets before,
    rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms HashTableValuesIn.journal_record_before
#print axioms evaluate_journalRecordSource_values_in
end InitECandidate.Runtime
