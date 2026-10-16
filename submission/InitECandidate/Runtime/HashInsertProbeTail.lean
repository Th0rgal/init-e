import InitECandidate.Runtime.HashInsertProbeReady
import InitECandidate.Runtime.HashInsertCopyTailOrdered
import InitECandidate.Runtime.HashFindIndex32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocated key-slot bounds and domains, independent of its current bytes. -/
structure HashInsertCopyBounds {F : Type} (table keys stride key keyLength used capacity index : BitVec 64)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  small : (keys + index * stride).toNat + keyLength.toNat ≤ 33806089496
  aligned : (keys + index * stride).toNat % 8 = 0
  sourceAligned : key.toNat % 8 = 0
  usedAligned : used.toNat % 8 = 0
  headerBefore : table.toNat + 72 ≤ (keys + index * stride).toNat
  copyBefore : (keys + index * stride).toNat + keyLength.toNat ≤ used.toNat
  usedBound : used.toNat + capacity.toNat ≤ 33806089496
  wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset)
  byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
  sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset)
  sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))

def hashInsertProbeTail : ProgHOL 64 := .seq hashProbeLoop hashInsertCopyTail

theorem source_htabInsert_probe_tail :
    sourceFindLocalScope (ofString "i") (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some (.dec (ofString "i") .one hashFindIndexExpression hashInsertProbeTail) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual insertion probe, key copy and all final stores, with a combined
capacity+keyLength+1 source-clock bound and an updated count invariant. -/
theorem evaluate_hashInsert_probe_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  obtain ⟨probed,slot,cell,probeRun,probeCost,probeRemaining,_,_,probeCode,addresses,_,ready,other⟩ :=
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
  obtain ⟨post,tail,header,agreement,cost,remaining⟩ := evaluate_hashInsert_copy_tail_ordered probed capacity used table values value
    order orderPos count slot cell keys stride key keyLength ready
    ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
    ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal) (probeCode.trans code)
    bounds.small bounds.aligned bounds.sourceAligned (by omega) words bytes sourceWords sourceBytes
    bounds.usedAligned bounds.headerBefore bounds.copyBefore bounds.usedBound
  refine ⟨post,?_,header,agreement,by omega,by omega⟩
  unfold hashInsertProbeTail
  rw [evaluateHOLFiniteState_seq_line780,probeRun]
  exact tail

#print axioms source_htabInsert_probe_tail
#print axioms evaluate_hashInsert_probe_tail
end InitECandidate.Runtime
