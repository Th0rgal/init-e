import InitECandidate.Runtime.HashInsertTailReady
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashInsertCopyTail : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memcpy")
    [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]) hashInsertValueTail

def sourceFirstCallSuffix (name : MlS) : ProgHOL 64 → Option (ProgHOL 64)
  | .seq (.call result callee args) rest =>
      if callee == name then some (.seq (.call result callee args) rest) else sourceFirstCallSuffix name rest
  | .dec _ _ _ body => sourceFirstCallSuffix name body
  | .decCall _ _ _ _ body => sourceFirstCallSuffix name body
  | .seq first rest => (sourceFirstCallSuffix name first).orElse (fun _ => sourceFirstCallSuffix name rest)
  | _ => none

theorem source_htabInsert_copy_tail :
    sourceFirstCallSuffix (ofString "memcpy") (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some hashInsertCopyTail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original insertion from the key copy through return: the header count and
actual occupancy count advance together within keyLength+1 source clocks. -/
theorem evaluate_hashInsert_copy_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      ∀ offset : Nat, offset < keyLength.toNat → watched ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  have arguments := eval_hashFind_arguments state keys index stride key keyLength keysLocal ready.indexLocal strideLocal keyLocal lengthLocal
  obtain ⟨copied,copyRun,counts,cost,remaining,_,_,addresses,endian,locals,frame⟩ :=
    evaluate_memcpy_aligned_call_with_frame state hashFindComparisonAddress (.var .local (ofString "key"))
      (.var .local (ofString "klen")) (keys + index * stride) key keyLength capacity used small aligned sourceAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate code arguments
  have protectedWords : ∀ watched ∈ ([table + 40,table + 24,panByteAlignHOL (used + index)] : List (BitVec 64)),
      copied.memory watched = state.memory watched := by
    intro watched member
    exact frame watched (watchedWords watched member) (watchedBytes watched member)
  have afterCopy := HashInsertTailReady.after_copy capacity used table values value order orderPos count index cell state copied
    ready locals addresses endian (protectedWords _ (by simp)) (protectedWords _ (by simp)) (protectedWords _ (by simp)) counts
  obtain ⟨post,tail,header,agreement,ticks⟩ := HashInsertTailReady.run capacity used table values value order orderPos count index cell copied afterCopy
  refine ⟨post,?_,header,agreement,by omega,by omega⟩
  unfold hashInsertCopyTail
  rw [evaluateHOLFiniteState_seq_line780,copyRun]
  exact tail

#print axioms source_htabInsert_copy_tail
#print axioms evaluate_hashInsert_copy_tail
end InitECandidate.Runtime
