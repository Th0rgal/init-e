import InitECandidate.Runtime.KeccakCopyTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original short-input remainder suffix, including pad zeroing, copy,
padding, absorption and aligned output, uses at most n+157 source ticks. -/
theorem evaluate_keccak_short_remainder_tail_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (remLocal : state.locals.lookup (ofString "rem") = some (.val (.word size)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 157 ≤ state.clock)
    (small : pad.toNat + 136 ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (shortInput : size.toNat < 136)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ result post, evaluateHOLFiniteState state keccakRemainderTail = (result,post) ∧
      state.clock ≤ post.clock + size.toNat + 157 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨middle,run,_,cost,remaining,globals,locals,postCode,domain,_⟩ :=
    evaluate_keccak_pad_zero_prefix state pad padGlobal code (by omega) small padAligned words bytes
  obtain ⟨result,post,tail,tailCost,tailRemaining,noTimeout⟩ :=
    evaluate_keccak_copy_tail_bounded middle pointer pad source size output
      (by rw [locals]; exact stp) (by rw [globals]; exact padGlobal)
      (by rw [locals]; exact p) (by rw [locals]; exact i)
      (by rw [locals]; exact remLocal) (by rw [locals]; exact outLocal)
      (postCode.trans code) (by omega) (by omega) padAligned sourceAligned outputAligned
      (by intro offset inside; rw [domain]; exact words offset (by omega))
      (by intro offset inside; rw [domain]; exact bytes offset (by omega))
      (by intro offset inside; rw [domain]; exact sourceWords offset inside)
      (by intro offset inside; rw [domain]; exact sourceBytes offset inside)
  exact ⟨result,post,run.trans tail,by omega,by omega,noTimeout⟩

#print axioms evaluate_keccak_short_remainder_tail_bounded
end InitECandidate.Runtime
