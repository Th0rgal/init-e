import InitECandidate.Runtime.HashInsertCopyEntries
import InitECandidate.Runtime.HashInsertValueEntries32
import InitECandidate.Runtime.HashInsertCopyOrderedMemory
import InitECandidate.Runtime.HashValueCopyGeometry32
import InitECandidate.Runtime.HashReverseCopyGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original 32-byte key-copy and insertion, with all separation premises
obtained from the table allocation layout. -/
theorem HashTableArraysInvariant32.insert_copy_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (sourceAligned : key.toNat % 8 = 0)
    (budget : 33 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < (32 : BitVec 64).toNat → state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < (32 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < (32 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < (32 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + (32 : BitVec 64).toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post := by
  have inside := ready.inside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have address := hashFind_slot_address keys index stride capacity ready.inside (by omega)
    invariant.keysAligned invariant.strideAligned
  have next := Nat.mul_le_mul_right stride.toNat (show index.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyBefore : (keys + index * stride).toNat + 32 ≤ used.toNat := by rw [address.1]; omega
  have small : (keys + index * stride).toNat + 32 ≤ 33806089496 := by omega
  have occupancy := memcpy_occupancy_separate (keys + index * stride) 32 used capacity
    address.2 invariant.usedAligned copyBefore (by omega)
  have watched := hashInsert_copy_watched_separate table (keys + index * stride) 32 used capacity index
    ready.inside address.2 invariant.usedAligned (by rw [address.1]; omega) copyBefore (by omega)
  obtain ⟨distinct,byteValues,bookkeeping⟩ := invariant.insert_value_separation state table keys stride capacity used values order orderPos count index bits ready.inside
  obtain ⟨newSeparate,reverseSeparate⟩ := invariant.insert_reverse_separation state table keys stride capacity used values order orderPos count index bits ready.inside
  exact evaluate_hashInsert_copy_entries state capacity used table values value order orderPos count index cell keys stride key 32
    ready keysLocal strideLocal keyLocal lengthLocal invariant.code small address.2 sourceAligned budget
    wordDomain byteDomain sourceWordDomain sourceByteDomain
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).1)
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).2)
    (fun word member offset inside => (watched word member offset inside).1)
    (fun word member offset inside => (watched word member offset inside).2)
    entries distinct byteValues bookkeeping reverseEntries
    (invariant.value_reverse_separate state table keys stride capacity used values order orderPos count index bits ready.inside)
    newSeparate reverseSeparate
    (invariant.delete_copy_values_separate state table keys stride capacity used values order orderPos count index bits ready.inside keysBeforeValues)
    (invariant.delete_copy_reverse_separate state table keys stride capacity used values order orderPos count index bits ready.inside)

#print axioms HashTableArraysInvariant32.insert_copy_entries
end InitECandidate.Runtime
