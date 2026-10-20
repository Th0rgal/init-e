import InitECandidate.Runtime.HashInsertProbeEntriesWidth
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesWidthKU
/-! Unaligned-key copy of `HashInsertProbeEntriesWidth` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original probe and insertion preserve all three entry invariants. -/
theorem evaluate_hashInsert_probe_entries_widthKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count initialIndex keys stride key keyLength : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word initialIndex)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (inside : initialIndex.toNat < capacity.toNat)
    (budget : capacity.toNat + keyLength.toNat + 1 ≤ state.clock)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (orderEntries : HashOrderEntriesBound order capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertProbeTail =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  change capacity.toNat + keyLength.toNat + 1 ≤ state.clock at budget
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have environment := facts.enter capacity used table values value order orderPos count state state
    rfl rfl rfl tableLocal orderLocal orderPosLocal usedLocal valueLocal
  have prepared := environment.prepare capacity used table values value order orderPos count state
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state used current = some byte := by
    intro current inRange
    have available := facts.byteDomain current inRange
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  have room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat := by
    rw [← invariant.agreement]
    exact invariant.room
  obtain ⟨probed,slot,cell,probeRun,probeCost,probeRemaining,probeMemory,probeGlobals,probeCode,addresses,probeEndian,ready,other⟩ :=
    evaluate_hashInsert_probe_ready state capacity used table values value order orderPos count initialIndex bits invariant.power
      indexLocal capacityLocal usedLocal inside (by omega) readable room prepared
  have probedInvariant := invariant.after_read state probed keyLength table keys stride capacity used values order orderPos count bits
    probeMemory probeCode addresses probeEndian
  have probedValues := entries.after_read state probed used values capacity probeMemory addresses probeEndian
  have probedReverse := reverseEntries.after_read state probed used orderPos capacity count probeMemory addresses probeEndian
  have probedOrder := orderEntries.after_memory state probed order capacity count probeMemory
  obtain ⟨post,tail,header,agreement,cost,remaining,words,reverse,ordered,globals,postCode,domain,endian⟩ :=
    probedInvariant.insert_copy_entries_widthKU probed capacity used table values value order orderPos count slot cell keys stride key keyLength bits
      ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.valueLocal
      ready.inside ready.byteMemory ready.empty
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      sourceAligned len8 keyFit (by omega)
      (by rw [addresses]; exact sourceWordDomain) (by rw [addresses]; exact sourceByteDomain)
      keysBeforeValues probedValues probedReverse probedOrder
  change probed.clock ≤ post.clock + keyLength.toNat + 1 at cost
  refine ⟨post,?_,header,agreement,by omega,by omega,words,reverse,ordered,
    globals.trans probeGlobals,postCode.trans probeCode,domain.trans addresses,endian.trans probeEndian⟩
  unfold hashInsertProbeTail
  rw [evaluateHOLFiniteState_seq_line780,probeRun]
  exact tail

#print axioms evaluate_hashInsert_probe_entries_widthKU
end InitECandidate.Runtime
