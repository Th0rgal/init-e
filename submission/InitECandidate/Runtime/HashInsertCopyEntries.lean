import InitECandidate.Runtime.HashInsertCopyMemory
import InitECandidate.Runtime.HashInsertValueEntries
import InitECandidate.Runtime.HashValueCopyFrame
import InitECandidate.Runtime.HashReverseCopyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original key-copy and insertion suffix while preserving both entry invariants. -/
theorem evaluate_hashInsert_copy_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (entries : HashValueEntriesWord used values capacity state)
    (distinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ index →
      values + slot * 8 ≠ values + index * 8)
    (byteValuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ panByteAlignHOL (used + index))
    (bookkeepingValuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      values + slot * 8 ≠ order + count * 8 ∧
      values + slot * 8 ≠ orderPos + index * 8 ∧ values + slot * 8 ≠ table + 24)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (valueReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + index * 8)
    (newSeparate : orderPos + index * 8 ≠ table + 24)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ index →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + index) ∧
      orderPos + slot * 8 ≠ order + count * 8 ∧
      orderPos + slot * 8 ≠ orderPos + index * 8 ∧ orderPos + slot * 8 ≠ table + 24)
    (valueCopySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      values + slot * 8 ≠ keys + index * stride + BitVec.ofNat 64 offset ∧
      values + slot * 8 ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
    (reverseCopySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      orderPos + slot * 8 ≠ keys + index * stride + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post := by
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
  have occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
      panByteAlignHOL (used + slot) ≠ keys + index * stride + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset) :=
    fun slot inside offset bound => ⟨wordSeparate offset bound slot inside,byteSeparate offset bound slot inside⟩
  have copiedValues := entries.copy_frame state copied used values capacity (keys + index * stride) keyLength
    addresses endian frame occupancy valueCopySeparate
  have copiedReverse := reverseEntries.copy_frame state copied used orderPos capacity count (keys + index * stride) keyLength
    addresses endian frame occupancy reverseCopySeparate
  obtain ⟨post,tail,header,agreement,ticks,words,reverse⟩ := evaluate_hashInsert_value_entries copied capacity used table values value order orderPos count index cell
    afterCopy.tableLocal afterCopy.orderLocal afterCopy.orderPosLocal afterCopy.usedLocal afterCopy.indexLocal afterCopy.valueLocal afterCopy.inside
    afterCopy.valuesDomain afterCopy.valuesMemory afterCopy.valueDomain afterCopy.byteDomain afterCopy.byteMemory afterCopy.empty
    afterCopy.orderDomain afterCopy.orderPosDomain afterCopy.countDomain afterCopy.countMemory afterCopy.agreement afterCopy.noWrap
    afterCopy.valueCountSeparate afterCopy.valueSeparate afterCopy.separate
    copiedValues distinct byteValuesSeparate bookkeepingValuesSeparate copiedReverse valueReverse newSeparate reverseSeparate
  refine ⟨post,?_,header,agreement,by omega,by omega,words,reverse⟩
  unfold hashInsertCopyTail
  rw [evaluateHOLFiniteState_seq_line780,copyRun]
  exact tail

#print axioms evaluate_hashInsert_copy_entries
end InitECandidate.Runtime
