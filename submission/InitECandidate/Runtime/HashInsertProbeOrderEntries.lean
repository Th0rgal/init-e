import InitECandidate.Runtime.HashInsertProbeMemory
import InitECandidate.Runtime.HashInsertCopyOrderedEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_probe_order_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (prepared : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot = some 0 →
      ∃ cell : BitVec 64, HashInsertTailReady capacity used table values value order orderPos count slot cell
        (setVarHOLFinite (ofString "i") (.val (.word slot)) state))
    (copyBounds : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → HashInsertCopyBounds table keys stride key keyLength used capacity slot state)
    (entries : HashOrderEntriesBound order capacity count state)
    (valuesAligned : values.toNat % 8 = 0) (orderAligned : order.toNat % 8 = 0)
    (reverseAligned : orderPos.toNat % 8 = 0)
    (headerOrder : table.toNat + 72 ≤ order.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (countRoom : count.toNat < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashInsertProbeTail =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  obtain ⟨probed,slot,cell,probeRun,probeCost,probeRemaining,probeMemory,probeGlobals,probeCode,addresses,probeEndian,ready,other⟩ :=
    evaluate_hashInsert_probe_ready state capacity used table values value order orderPos count initialIndex bits power
      indexLocal capacityLocal usedLocal inside (by omega) readable room prepared
  have bounds := copyBounds slot ready.inside
  have words : ∀ offset : Nat, offset < keyLength.toNat → probed.memaddrs (keys + slot * stride + BitVec.ofNat 64 offset) := by
    rw [addresses]; exact bounds.wordDomain
  have bytes : ∀ offset : Nat, offset < keyLength.toNat → probed.memaddrs (panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) := by
    rw [addresses]; exact bounds.byteDomain
  have sourceWords : ∀ offset : Nat, offset < keyLength.toNat → probed.memaddrs (key + BitVec.ofNat 64 offset) := by
    rw [addresses]; exact bounds.sourceWordDomain
  have sourceBytes : ∀ offset : Nat, offset < keyLength.toNat → probed.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)) := by
    rw [addresses]; exact bounds.sourceByteDomain
  have probedEntries := entries.after_memory state probed order capacity count probeMemory
  obtain ⟨post,tail,valid,header,agreement,cost,remaining⟩ := evaluate_hashInsert_copy_ordered_entries probed capacity used table values value
    order orderPos count slot cell keys stride key keyLength ready
    ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
    ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal) (probeCode.trans code)
    bounds.small bounds.aligned bounds.sourceAligned (by omega) words bytes sourceWords sourceBytes
    bounds.usedAligned bounds.headerBefore bounds.copyBefore bounds.usedBound probedEntries valuesAligned orderAligned reverseAligned
    headerOrder valuesBefore usedBefore orderBefore bounded countRoom
  refine ⟨post,?_,valid,header,agreement,by omega,by omega⟩
  unfold hashInsertProbeTail
  rw [evaluateHOLFiniteState_seq_line780,probeRun]
  exact tail

#print axioms evaluate_hashInsert_probe_order_entries
end InitECandidate.Runtime
