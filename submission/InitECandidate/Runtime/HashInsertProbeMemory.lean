import InitECandidate.Runtime.HashInsertProbeTail
import InitECandidate.Runtime.HashInsertCopyOrderedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Probe-to-return insertion preserves metadata and words outside every
possible selected slot's copy and store destinations. -/
theorem evaluate_hashInsert_probe_tail_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (copyBounds : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → HashInsertCopyBounds table keys stride key keyLength used capacity slot state) :
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
  obtain ⟨post,tail,header,agreement,cost,remaining,tailGlobals,tailCode,tailAddresses,tailEndian,tailFrame⟩ := evaluate_hashInsert_copy_tail_ordered_memory probed capacity used table values value
    order orderPos count slot cell keys stride key keyLength ready
    ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
    ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal) (probeCode.trans code)
    bounds.small bounds.aligned bounds.sourceAligned (by omega) words bytes sourceWords sourceBytes
    bounds.usedAligned bounds.headerBefore bounds.copyBefore bounds.usedBound
  refine ⟨post,?_,header,agreement,by omega,by omega,tailGlobals.trans probeGlobals,tailCode.trans probeCode,
    tailAddresses.trans addresses,tailEndian.trans probeEndian,?_⟩
  · unfold hashInsertProbeTail
    rw [evaluateHOLFiniteState_seq_line780,probeRun]
    exact tail
  · intro watched copySeparate storesSeparate orderSeparate countSeparate
    have stores := storesSeparate slot ready.inside
    have preserved := tailFrame watched
      (fun offset inside => (copySeparate slot ready.inside offset inside).1)
      (fun offset inside => (copySeparate slot ready.inside offset inside).2)
      stores.1 stores.2.1 orderSeparate stores.2.2 countSeparate
    rw [preserved,probeMemory]

#print axioms evaluate_hashInsert_probe_tail_memory
end InitECandidate.Runtime
