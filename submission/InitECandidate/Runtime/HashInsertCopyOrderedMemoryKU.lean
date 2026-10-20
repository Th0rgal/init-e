import InitECandidate.Runtime.HashInsertCopyOrderedMemory
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertCopyMemoryKU
/-! Unaligned-key copy of `HashInsertCopyOrderedMemory` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Ordered header/key/occupancy allocations discharge all copy separation
premises of the actual insertion copy-and-count suffix. -/
theorem evaluate_hashInsert_copy_tail_ordered_memoryKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key keyLength : BitVec 64)
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (code : state.code = originalRuntimeCode)
    (small : (keys + index * stride).toNat + keyLength.toNat ≤ 33806089496)
    (aligned : (keys + index * stride).toNat % 8 = 0) (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ (keys + index * stride).toNat)
    (copyBefore : (keys + index * stride).toNat + keyLength.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64,
        (∀ offset : Nat, offset < keyLength.toNat → watched ≠ keys + index * stride + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < keyLength.toNat → watched ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) →
        watched ≠ values + index * 8 → watched ≠ panByteAlignHOL (used + index) →
        watched ≠ order + count * 8 → watched ≠ orderPos + index * 8 → watched ≠ table + 24 →
        post.memory watched = state.memory watched := by
  have occupancy := memcpy_occupancy_separate (keys + index * stride) keyLength used capacity
    aligned usedAligned copyBefore usedBound
  have watched := hashInsert_copy_watched_separate table (keys + index * stride) keyLength used capacity index
    ready.inside aligned usedAligned headerBefore copyBefore usedBound
  exact evaluate_hashInsert_copy_tail_memoryKU state capacity used table values value order orderPos count index cell keys stride key keyLength
    ready keysLocal strideLocal keyLocal lengthLocal code small aligned sourceAligned len8 keyFit budget wordDomain byteDomain sourceWordDomain sourceByteDomain
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).1)
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).2)
    (fun word member offset inside => (watched word member offset inside).1)
    (fun word member offset inside => (watched word member offset inside).2)

#print axioms evaluate_hashInsert_copy_tail_ordered_memoryKU
end InitECandidate.Runtime
