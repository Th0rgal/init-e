import InitECandidate.Runtime.HashInsertValueLinkedWidth
import InitECandidate.Runtime.HashInsertCopyEntries
import InitECandidate.Runtime.HashInsertCopyBounds
import InitECandidate.Runtime.HashTableArraysCopyFrameWidth
import InitECandidate.Runtime.HashOrderLinkedCopyWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual key copying followed by insertion preserves the live order link. -/
theorem HashTableArraysInvariant.insert_copy_linked_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key keyLength : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (sourceAligned : key.toNat % 8 = 0)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashOrderLinked used order orderPos capacity (count + 1) post := by
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address := by
    intro address lower upper
    apply invariant.domain <;> omega
  have bounds := hashInsert_copy_bounds_from_array state table keys stride key keyLength used capacity
    invariant.keysAligned invariant.strideAligned sourceAligned invariant.usedAligned hk ku (by omega)
    invariant.fits arrayDomain sourceWordDomain sourceByteDomain index inside
  have occupancy := memcpy_occupancy_separate (keys + index * stride) keyLength used capacity
    bounds.aligned invariant.usedAligned bounds.copyBefore (by omega)
  have arguments := eval_hashFind_arguments state keys index stride key keyLength keysLocal indexLocal strideLocal keyLocal lengthLocal
  obtain ⟨copied,copyRun,_,cost,remaining,_,copyCode,addresses,endian,locals,frame⟩ :=
    evaluate_memcpy_aligned_call_with_frame state hashFindComparisonAddress (.var .local (ofString "key"))
      (.var .local (ofString "klen")) (keys + index * stride) key keyLength capacity used bounds.small bounds.aligned sourceAligned budget
      bounds.wordDomain bounds.byteDomain sourceWordDomain sourceByteDomain
      (fun offset small slot bound => (occupancy offset small slot bound).1)
      (fun offset small slot bound => (occupancy offset small slot bound).2) invariant.code arguments
  have copiedInvariant := invariant.key_copy_frame_width state copied keyLength table keys stride capacity used values order orderPos count index bits
    inside copyCode addresses endian frame
  have copiedLinked := linked.copy_frame_layout_width state copied keyLength table keys stride capacity used values order orderPos count index bits
    invariant inside addresses endian frame
  have occupancyFrame := (invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos count index index bits inside inside).1
  have byteAfter : copied.memory (panByteAlignHOL (used + index)) = .word cell := by
    rw [frame _ (fun offset small => (occupancyFrame index inside offset small).1)
      (fun offset small => (occupancyFrame index inside offset small).2)]
    exact byteMemory
  obtain ⟨post,tail,ticks,postLinked⟩ := evaluate_hashInsert_value_linked_width copied
    keyLength table keys stride capacity used values order orderPos count index value cell bits copiedInvariant copiedLinked inside
    (by rw [locals]; exact tableLocal) (by rw [locals]; exact orderLocal)
    (by rw [locals]; exact orderPosLocal) (by rw [locals]; exact usedLocal)
    (by rw [locals]; exact indexLocal) (by rw [locals]; exact valueLocal) byteAfter
  refine ⟨post,?_,by change state.clock ≤ copied.clock + keyLength.toNat + 1 at cost; omega,by omega,postLinked⟩
  unfold hashInsertCopyTail
  rw [evaluateHOLFiniteState_seq_line780,copyRun]
  exact tail

#print axioms HashTableArraysInvariant.insert_copy_linked_width
end InitECandidate.Runtime
