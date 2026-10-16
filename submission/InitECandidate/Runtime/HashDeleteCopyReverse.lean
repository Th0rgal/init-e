import InitECandidate.Runtime.HashDeleteCopyFrame
import InitECandidate.Runtime.HashReverseCopyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_copy_reverse {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size watched used orderPos capacity items : BitVec 64)
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
    (wordSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ (keys + hole * stride) + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < size.toNat → watched ≠ panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      panByteAlignHOL (used + slot) ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      orderPos + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
 :
    ∃ copied, evaluateHOLFiniteState state hashDeleteMoveBody =
        evaluateHOLFiniteState copied hashDeleteValueTail ∧
      copied.memory watched = state.memory watched ∧
      state.clock ≤ copied.clock + size.toNat + 1 ∧ copied.clock ≤ state.clock ∧
      copied.globals = state.globals ∧ copied.code = state.code ∧
      copied.memaddrs = state.memaddrs ∧ copied.be = state.be ∧ copied.locals = state.locals ∧
      (∀ cell : BitVec 64,
        (∀ offset : Nat, offset < size.toNat → cell ≠ keys + hole * stride + BitVec.ofNat 64 offset) →
        (∀ offset : Nat, offset < size.toNat → cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset)) →
        copied.memory cell = state.memory cell) ∧ HashReverseEntriesBound used orderPos capacity items copied := by
  obtain ⟨copied,run,watchedCell,cost,remaining,globals,postCode,addresses,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan size watched keysLocal strideLocal holeLocal scanLocal sizeLocal
      small aligned scanAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain wordSeparate byteSeparate code
  exact ⟨copied,run,watchedCell,cost,remaining,globals,postCode,addresses,endian,locals,frame,
    entries.copy_frame state copied used orderPos capacity items (keys + hole * stride) size addresses endian
      frame occupancySeparate reverseSeparate⟩

#print axioms evaluate_hashDelete_copy_reverse
end InitECandidate.Runtime
