import InitECandidate.Runtime.HashDeleteCopyFrame
import InitECandidate.Runtime.JournalUndoRecords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual deletion memcpy preserves every disjoint live journal record. -/
theorem evaluate_hashDelete_copy_journal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size journal : BitVec 64) (count : Nat)
    (valid : JournalUndoRecords journal count state) (positive : 0 < count)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (small : (keys + hole * stride).toNat + size.toNat ≤ 33806089496)
    (aligned : (keys + hole * stride).toNat % 8 = 0) (scanAligned : (keys + scan * stride).toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs ((keys + scan * stride) + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL ((keys + scan * stride) + BitVec.ofNat 64 offset)))
    (wordSeparate : ∀ index : Nat, index < count → ∀ field ∈ ([0,8,16,24] : List Nat),
      ∀ offset : Nat, offset < size.toNat → journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 field ≠ (keys + hole * stride) + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ index : Nat, index < count → ∀ field ∈ ([0,8,16,24] : List Nat),
      ∀ offset : Nat, offset < size.toNat → journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 field ≠ panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
 :
    ∃ copied, evaluateHOLFiniteState state hashDeleteMoveBody = evaluateHOLFiniteState copied hashDeleteValueTail ∧
      JournalUndoRecords journal count copied ∧
      state.clock ≤ copied.clock + size.toNat + 1 ∧ copied.clock ≤ state.clock ∧
      copied.globals = state.globals ∧ copied.code = state.code ∧ copied.memaddrs = state.memaddrs ∧
      copied.be = state.be ∧ copied.locals = state.locals := by
  have firstWord : ∀ offset : Nat, offset < size.toNat → journal ≠ keys + hole * stride + BitVec.ofNat 64 offset := by
    simpa using wordSeparate 0 positive 0 (by simp)
  have firstByte : ∀ offset : Nat, offset < size.toNat → journal ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset) := by
    simpa using byteSeparate 0 positive 0 (by simp)
  obtain ⟨copied,run,_,cost,remaining,globals,postCode,domain,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan size journal keysLocal strideLocal holeLocal scanLocal sizeLocal
      small aligned scanAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain firstWord firstByte code
  refine ⟨copied,run,?_,cost,remaining,globals,postCode,domain,endian,locals⟩
  apply valid.after_frame (after := copied) (Nat.le_refl _) domain
  intro index inside field member
  exact frame _ (wordSeparate index inside field member) (byteSeparate index inside field member)

#print axioms evaluate_hashDelete_copy_journal
end InitECandidate.Runtime
