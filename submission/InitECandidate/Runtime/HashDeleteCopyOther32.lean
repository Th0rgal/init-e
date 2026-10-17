import InitECandidate.Runtime.HashDeleteCopy
import InitECandidate.Runtime.HashTableReadyMemcpy32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original deletion key copy preserves a disjoint ready table. -/
theorem evaluate_hashDelete_copy_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size : BitVec 64)
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
    (table pointer otherKeys otherStride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table otherKeys otherStride capacity used values order orderPos items bits pointer state)
    (outside : (keys + hole * stride).toNat + size.toNat ≤ table.toNat ∨
      orderPos.toNat + capacity.toNat * 8 ≤ (keys + hole * stride).toNat) :
    ∃ copied, evaluateHOLFiniteState state hashDeleteMoveBody = evaluateHOLFiniteState copied hashDeleteValueTail ∧
      HashTableReady32 table otherKeys otherStride capacity used values order orderPos items bits pointer copied ∧
      state.clock ≤ copied.clock + size.toNat + 1 ∧ copied.clock ≤ state.clock ∧
      copied.globals = state.globals ∧ copied.code = state.code ∧ copied.memaddrs = state.memaddrs ∧
      copied.be = state.be ∧ copied.locals = state.locals := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [hashDeleteCopyAddress (ofString "i"),hashDeleteCopyAddress (ofString "j"),.var .local (ofString "klen")] =
      some [.val (.word (keys + hole * stride)),.val (.word (keys + scan * stride)),.val (.word size)] := by
    simp [hashDeleteCopyAddress,evalListHOLFinite,evalListHOLExact,evalHOLExact,
      keysLocal,strideLocal,holeLocal,scanLocal,sizeLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  obtain ⟨copied,run,preserved,cost,remaining,globals,postCode,addresses,endian,locals⟩ :=
    ready.memcpy_outside state table pointer otherKeys otherStride capacity used values order orderPos items bits
      _ _ _ (keys + hole * stride) (keys + scan * stride) size small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain outside arguments
  refine ⟨copied,?_,preserved,cost,remaining,globals,postCode,addresses,endian,locals⟩
  rw [source_hashDelete_copy_body,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_hashDelete_copy_other
end InitECandidate.Runtime
