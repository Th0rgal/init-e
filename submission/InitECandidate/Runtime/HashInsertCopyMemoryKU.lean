import InitECandidate.Runtime.HashInsertCopyMemory
import InitECandidate.Runtime.PtKeyULeafKUGD
/-! Unaligned-key copy of `HashInsertCopyMemory` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real copy-and-insert suffix preserves metadata and every separate word. -/
theorem evaluate_hashInsert_copy_tail_memoryKU {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (wordSeparate : ∀ offset : Nat, offset < keyLength.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ keys + index * stride + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < keyLength.toNat → ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))
    (watchedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat → watched ≠ keys + index * stride + BitVec.ofNat 64 offset)
    (watchedBytes : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat → watched ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) :
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
  have arguments := eval_hashFind_arguments state keys index stride key keyLength keysLocal ready.indexLocal strideLocal keyLocal lengthLocal
  obtain ⟨copied,copyRun,counts,cost,remaining,copyGlobals,copyCode,addresses,endian,locals,frame⟩ :=
    evaluate_memcpy_aligned_call_with_frameKU state hashFindComparisonAddress (.var .local (ofString "key"))
      (.var .local (ofString "klen")) (keys + index * stride) key keyLength capacity used small aligned sourceAligned len8 keyFit budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate code arguments
  have protectedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      copied.memory watched = state.memory watched := by
    intro watched member
    exact frame watched (watchedWords watched member) (watchedBytes watched member)
  have afterCopy := HashInsertTailReady.after_copy capacity used table values value order orderPos count index cell state copied
    ready locals addresses endian (protectedWords _ (by simp)) (protectedWords _ (by simp)) (protectedWords _ (by simp)) counts
  obtain ⟨post,tail,header,agreement,ticks,tailGlobals,tailCode,tailAddresses,tailEndian,tailFrame⟩ := HashInsertTailReady.run_memory capacity used table values value order orderPos count index cell copied afterCopy
  refine ⟨post,?_,header,agreement,by omega,by omega,tailGlobals.trans copyGlobals,tailCode.trans copyCode,
    tailAddresses.trans addresses,tailEndian.trans endian,?_⟩
  · unfold hashInsertCopyTail
    rw [evaluateHOLFiniteState_seq_line780,copyRun]
    exact tail
  · intro watched words bytes valueCell byte first second third
    exact (tailFrame watched valueCell byte first second third).trans (frame watched words bytes)

#print axioms evaluate_hashInsert_copy_tail_memoryKU
end InitECandidate.Runtime
