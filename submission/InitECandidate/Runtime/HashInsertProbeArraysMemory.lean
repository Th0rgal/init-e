import InitECandidate.Runtime.HashInsertSlotEnvironment
import InitECandidate.Runtime.HashInsertProbeMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shared table locals, allocated arrays and empty-slot facts discharge the
per-slot preparation premises of the original insertion probe-to-return proof. -/
theorem evaluate_hashInsert_probe_tail_from_arrays_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count initialIndex keys stride key keyLength : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (code : state.code = originalRuntimeCode)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word initialIndex)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (inside : initialIndex.toNat < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 1 ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (environment : HashInsertSlotEnvironment capacity used table values value order orderPos count state)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state hashInsertProbeTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
          watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
          watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) →
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
          watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) →
        watched ≠ order + count * 8 → watched ≠ table + 24 → post.memory watched = state.memory watched := by
  exact evaluate_hashInsert_probe_tail_memory state capacity used table values value order orderPos count initialIndex keys stride key keyLength bits
    power code indexLocal capacityLocal usedLocal keysLocal strideLocal keyLocal lengthLocal inside budget readable room
    (fun slot inside empty => HashInsertSlotEnvironment.prepare capacity used table values value order orderPos count state environment slot inside empty)
    (hashInsert_copy_bounds_from_array state table keys stride key keyLength used capacity keysAligned strideAligned keyAligned usedAligned
      headerBefore keysBefore usedBound fits arrayDomain sourceWordDomain sourceByteDomain)

#print axioms evaluate_hashInsert_probe_tail_from_arrays_memory
end InitECandidate.Runtime
