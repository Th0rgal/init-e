import InitECandidate.Runtime.KeccakCopyPrefix
import InitECandidate.Runtime.MemcpyAlignedCallCells
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.KeccakZeroPrefixesCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_keccak_short_copy_prefix_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pad source size : BitVec 64)
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (remLocal : state.locals.lookup (ofString "rem") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 1 ≤ state.clock)
    (small : pad.toNat + size.toNat ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (bytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state keccakAfterPadZero = evaluateHOLFiniteState post keccakAfterCopy ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .global (ofString "keccak_pad"),.op .add [.var .local (ofString "p"),.var .local (ofString "i")],.var .local (ofString "rem")] =
      some [.val (.word pad),.val (.word source),.val (.word size)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,padGlobal,p,i,remLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals⟩ := evaluate_memcpy_aligned_call_cells state _ _ _ pad source size 0 0
    small padAligned sourceAligned ticks
    (aligned_word_domain_of_byte_domain_modular state pad size padAligned bytes) bytes
    (aligned_word_domain_of_byte_domain_modular state source size sourceAligned sourceBytes) sourceBytes
    (by intro offset inside slot impossible; change slot.toNat < 0 at impossible; omega)
    (by intro offset inside slot impossible; change slot.toNat < 0 at impossible; omega) code args
  refine ⟨post,?_,cost,remaining,globals,locals,postCode,domain,endian⟩
  rw [source_keccak_copy_prefix,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_keccak_short_copy_prefix_cells
end InitECandidate.Runtime
