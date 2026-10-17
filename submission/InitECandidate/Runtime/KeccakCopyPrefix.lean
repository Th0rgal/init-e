import InitECandidate.Runtime.KeccakZeroPrefixes
import InitECandidate.Runtime.MemcpyAlignedCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakAfterCopy : ProgHOL 64 :=
  match keccakAfterPadZero with
  | .seq _ tail => tail
  | _ => .skip

theorem source_keccak_copy_prefix : keccakAfterPadZero =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.var .global (ofString "keccak_pad"),.op .add [.var .local (ofString "p"),.var .local (ofString "i")],.var .local (ofString "rem")]) keccakAfterCopy := by
  simp only [keccakAfterCopy,keccakAfterPadZero,keccakRemainderTail,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original short-input copy prefix reaches padding with its source
length bound and all globals and caller locals preserved. -/
theorem evaluate_keccak_short_copy_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pad source size : BitVec 64)
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (remLocal : state.locals.lookup (ofString "rem") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 1 ≤ state.clock)
    (small : pad.toNat + size.toNat ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < size.toNat → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state keccakAfterPadZero = evaluateHOLFiniteState post keccakAfterCopy ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .global (ofString "keccak_pad"),.op .add [.var .local (ofString "p"),.var .local (ofString "i")],.var .local (ofString "rem")] =
      some [.val (.word pad),.val (.word source),.val (.word size)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,padGlobal,p,i,remLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals⟩ := evaluate_memcpy_aligned_call state _ _ _ pad source size 0 0
    small padAligned sourceAligned ticks words bytes sourceWords sourceBytes
    (by intro offset inside slot impossible; change slot.toNat < 0 at impossible; omega)
    (by intro offset inside slot impossible; change slot.toNat < 0 at impossible; omega) code args
  refine ⟨post,?_,cost,remaining,globals,locals,postCode,domain,endian⟩
  rw [source_keccak_copy_prefix,evaluateHOLFiniteState_seq_line780,run]

#print axioms source_keccak_copy_prefix
#print axioms evaluate_keccak_short_copy_prefix
end InitECandidate.Runtime
