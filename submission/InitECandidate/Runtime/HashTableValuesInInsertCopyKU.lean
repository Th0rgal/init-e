import InitECandidate.Runtime.HashTableValuesInInsertCopy
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
import InitECandidate.Runtime.HashInsertProbeEntriesWidthKU
import InitECandidate.Runtime.HashInsertIndexEntriesWidthKU
import InitECandidate.Runtime.HashInsertHashAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertBodyAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
import InitECandidate.Runtime.HashInsertIndexLinkedWidthKU
import InitECandidate.Runtime.HashInsertHashLinkedSupportedKU
import InitECandidate.Runtime.HashInsertBodyLinkedSupportedKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCallLinkedSupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
import InitECandidate.Runtime.HashTableArraysFrameSupportedKU
import InitECandidate.Runtime.HashTableArraysAllEntriesSupportedKU
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertSupportedKU
/-! Unaligned-key copy of `HashTableValuesInInsertCopy` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original key-copy and insertion suffix retains registered-pointer
membership through the actual memcpy call, occupancy mark, and bookkeeping. -/
theorem HashTableArraysInvariant.insert_copy_values_inKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key keyLength : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (sourceAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧ post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have ready : HashInsertTailReady capacity used table values value order orderPos count index cell state := {
    tableLocal := tableLocal
    orderLocal := orderLocal
    orderPosLocal := orderPosLocal
    usedLocal := usedLocal
    indexLocal := indexLocal
    valueLocal := valueLocal
    inside := inside
    valuesDomain := facts.valuesDomain
    valuesMemory := facts.valuesMemory
    valueDomain := facts.valueDomain index inside
    byteDomain := facts.byteDomain index inside
    byteMemory := byteMemory
    empty := empty
    orderDomain := facts.orderDomain
    orderPosDomain := facts.orderPosDomain index inside
    countDomain := facts.countDomain
    countMemory := facts.countMemory
    agreement := facts.agreement
    noWrap := facts.noWrap
    valueCountSeparate := facts.valueCountSeparate index inside
    valueSeparate := facts.valueSeparate index inside
    separate := facts.separate index inside
  }
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address := by
    intro address lower upper
    apply invariant.domain <;> omega
  have bounds := hashInsert_copy_bounds_from_arrayKU state table keys stride key keyLength used capacity
    invariant.keysAligned invariant.strideAligned sourceAligned len8 keyFit invariant.usedAligned hk ku (by omega)
    invariant.fits arrayDomain sourceWordDomain sourceByteDomain index inside
  have occupancy := memcpy_occupancy_separate (keys + index * stride) keyLength used capacity
    bounds.aligned invariant.usedAligned bounds.copyBefore (by omega)
  have watched := hashInsert_copy_watched_separate table (keys + index * stride) keyLength used capacity index
    ready.inside bounds.aligned invariant.usedAligned bounds.headerBefore bounds.copyBefore (by omega)
  have arguments := eval_hashFind_arguments state keys index stride key keyLength keysLocal indexLocal strideLocal keyLocal lengthLocal
  obtain ⟨copied,copyRun,counts,cost,remaining,copyGlobals,copyCode,addresses,endian,locals,frame⟩ :=
    evaluate_memcpy_aligned_call_with_frameKU state hashFindComparisonAddress (.var .local (ofString "key"))
      (.var .local (ofString "klen")) (keys + index * stride) key keyLength capacity used bounds.small bounds.aligned sourceAligned len8 keyFit budget
      bounds.wordDomain bounds.byteDomain sourceWordDomain sourceByteDomain
      (fun offset bound slot inside => (occupancy offset bound slot inside).1)
      (fun offset bound slot inside => (occupancy offset bound slot inside).2) invariant.code arguments
  have protectedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      copied.memory watched = state.memory watched := by
    intro word atWord
    exact frame word (fun byte bound => (watched word atWord byte bound).1) (fun byte bound => (watched word atWord byte bound).2)
  have afterCopy := HashInsertTailReady.after_copy capacity used table values value order orderPos count index cell state copied
    ready locals addresses endian (protectedWords _ (by simp)) (protectedWords _ (by simp)) (protectedWords _ (by simp)) counts
  have copiedArrays := invariant.key_copy_frame_width state copied keyLength table keys stride capacity used values order orderPos count index bits
    inside copyCode addresses endian frame
  have copiedEntries := entries.key_copy_frame state copied keyLength table keys stride capacity used values order orderPos count index bits
    invariant targets inside keysBeforeValues addresses endian frame
  obtain ⟨post,tail,preserved,header,agreement,clock,globals,code,domain,lastEndian⟩ :=
    copiedArrays.insert_values_in copied keyLength table keys stride capacity used values value order orderPos count index cell bits
      afterCopy.tableLocal afterCopy.orderLocal afterCopy.orderPosLocal afterCopy.usedLocal afterCopy.indexLocal afterCopy.valueLocal
      afterCopy.inside afterCopy.byteMemory afterCopy.empty targets copiedEntries member
  refine ⟨post,?_,preserved,header,agreement,by omega,by omega,globals.trans copyGlobals,code.trans copyCode,domain.trans addresses,lastEndian.trans endian⟩
  unfold hashInsertCopyTail
  rw [evaluateHOLFiniteState_seq_line780,copyRun]
  exact tail

#print axioms HashTableArraysInvariant.insert_copy_values_inKU
end InitECandidate.Runtime
