import InitECandidate.Runtime.HashInsertCopyOrderEntries
import InitECandidate.Runtime.HashInsertCopyOrderedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_copy_ordered_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key keyLength : BitVec 64)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (code : state.code = originalRuntimeCode)
    (small : (keys + index * stride).toNat + keyLength.toNat ≤ 33806089496)
    (aligned : (keys + index * stride).toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ (keys + index * stride).toNat)
    (copyBefore : (keys + index * stride).toNat + keyLength.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496)
    (entries : HashOrderEntriesBound order capacity count state)
    (valuesAligned : values.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (headerOrder : table.toNat + 72 ≤ order.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : count.toNat < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  have occupancy := memcpy_occupancy_separate (keys + index * stride) keyLength used capacity
    aligned usedAligned copyBefore usedBound
  have watched := hashInsert_copy_watched_separate table (keys + index * stride) keyLength used capacity index
    ready.inside aligned usedAligned headerBefore copyBefore usedBound
  have orderSeparate : ∀ position : BitVec 64, position.toNat < count.toNat →
      ∀ offset : Nat, offset < keyLength.toNat →
      order + position * 8 ≠ keys + index * stride + BitVec.ofNat 64 offset ∧
      order + position * 8 ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset) := by
    intro position before
    have address := (hashFind_slot_address order position 8 capacity (by omega)
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) orderAligned (by decide)).1
    change (order + position * 8).toNat = order.toNat + position.toNat * 8 at address
    apply memcpy_interval_separate (keys + index * stride) keyLength (order + position * 8) aligned small
    right
    omega
  exact evaluate_hashInsert_copy_order_entries state capacity used table values value order orderPos count index cell keys stride key keyLength
    ready keysLocal strideLocal keyLocal lengthLocal code small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).1)
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).2)
    (fun word member offset inside => (watched word member offset inside).1)
    (fun word member offset inside => (watched word member offset inside).2)
    entries valuesAligned usedAligned orderAligned reverseAligned headerOrder valuesBefore usedBefore orderBefore bounded room
    (fun position before offset inside => (orderSeparate position before offset inside).1)
    (fun position before offset inside => (orderSeparate position before offset inside).2)

#print axioms evaluate_hashInsert_copy_ordered_entries
end InitECandidate.Runtime
