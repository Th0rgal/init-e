import InitECandidate.Runtime.HashInsertCopyMemory
import InitECandidate.Runtime.HashInsertTailOrderEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_copy_order_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (wordSeparate : ∀ offset : Nat, offset < keyLength.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ keys + index * stride + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < keyLength.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
    (watchedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat → watched ≠ keys + index * stride + BitVec.ofNat 64 offset)
    (watchedBytes : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat → watched ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
    (entries : HashOrderEntriesBound order capacity count state)
    (valuesAligned : values.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (reverseAligned : orderPos.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ order.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (room : count.toNat < capacity.toNat)
    (orderWords : ∀ position : BitVec 64, position.toNat < count.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      order + position * 8 ≠ keys + index * stride + BitVec.ofNat 64 offset)
    (orderBytes : ∀ position : BitVec 64, position.toNat < count.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      order + position * 8 ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  have arguments := eval_hashFind_arguments state keys index stride key keyLength keysLocal ready.indexLocal strideLocal keyLocal lengthLocal
  obtain ⟨copied,copyRun,counts,cost,remaining,copyGlobals,copyCode,addresses,endian,locals,frame⟩ :=
    evaluate_memcpy_aligned_call_with_frame state hashFindComparisonAddress (.var .local (ofString "key"))
      (.var .local (ofString "klen")) (keys + index * stride) key keyLength capacity used small aligned sourceAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate code arguments
  have protectedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      copied.memory watched = state.memory watched := by
    intro watched member
    exact frame watched (watchedWords watched member) (watchedBytes watched member)
  have afterCopy := HashInsertTailReady.after_copy capacity used table values value order orderPos count index cell state copied
    ready locals addresses endian (protectedWords _ (by simp)) (protectedWords _ (by simp)) (protectedWords _ (by simp)) counts
  have copiedEntries : HashOrderEntriesBound order capacity count copied := by
    intro position before
    obtain ⟨slot,memory,valid⟩ := entries position before
    exact ⟨slot,(frame _ (orderWords position before) (orderBytes position before)).trans memory,valid⟩
  obtain ⟨post,tail,valid,header,agreement,ticks⟩ := afterCopy.run_order_entries
    capacity used table values value order orderPos count index cell copied copiedEntries valuesAligned usedAligned
    orderAligned reverseAligned headerBefore valuesBefore usedBefore orderBefore bounded room
  refine ⟨post,?_,valid,header,agreement,by omega,by omega⟩
  unfold hashInsertCopyTail
  rw [evaluateHOLFiniteState_seq_line780,copyRun]
  exact tail

#print axioms evaluate_hashInsert_copy_order_entries
end InitECandidate.Runtime
