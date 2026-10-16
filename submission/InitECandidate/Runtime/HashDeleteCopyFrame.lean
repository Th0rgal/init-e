import InitECandidate.Runtime.HashDeleteCopy
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_copy_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size watched : BitVec 64)
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
        copied.memory cell = state.memory cell) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [hashDeleteCopyAddress (ofString "i"),hashDeleteCopyAddress (ofString "j"),.var .local (ofString "klen")] =
      some [.val (.word (keys + hole * stride)),.val (.word (keys + scan * stride)),.val (.word size)] := by
    simp [hashDeleteCopyAddress,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      keysLocal,strideLocal,holeLocal,scanLocal,sizeLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨copied,run,frame,cost,remaining,globals,postCode,addresses,endian,locals⟩ :=
    evaluate_memcpy_aligned_frame_call state _ _ _ (keys + hole * stride) (keys + scan * stride) size watched
      small aligned scanAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
      wordSeparate byteSeparate code arguments
  refine ⟨copied,?_,frame,cost,remaining,globals,postCode,addresses,endian,locals,?_⟩
  · rw [source_hashDelete_copy_body,evaluateHOLFiniteState_seq_line780,run]
  · intro cell words bytes
    obtain ⟨checked,checkedRun,checkedFrame,_⟩ :=
      evaluate_memcpy_aligned_frame_call state _ _ _ (keys + hole * stride) (keys + scan * stride) size cell
        small aligned scanAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
        words bytes code arguments
    have same := congrArg Prod.snd (run.symm.trans checkedRun)
    change copied = checked at same
    rw [same]
    exact checkedFrame

#print axioms evaluate_hashDelete_copy_frame
end InitECandidate.Runtime
