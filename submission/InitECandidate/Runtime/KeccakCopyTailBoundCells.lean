import InitECandidate.Runtime.KeccakCopyTailBound
import InitECandidate.Runtime.KeccakCopyPrefixCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_keccak_copy_tail_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (remLocal : state.locals.lookup (ofString "rem") = some (.val (.word size)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 20 ≤ state.clock)
    (small : pad.toNat + size.toNat ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (bytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ result post, evaluateHOLFiniteState state keccakAfterPadZero = (result,post) ∧
      state.clock ≤ post.clock + size.toNat + 20 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨middle,run,cost,remaining,globals,locals,postCode,_,_⟩ :=
    evaluate_keccak_short_copy_prefix_cells state pad source size padGlobal p i remLocal code
      (by omega) small padAligned sourceAligned bytes sourceBytes
  have stpMiddle : middle.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    rw [locals]; exact stp
  have padMiddle : middle.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
    rw [globals]; exact padGlobal
  have outMiddle : middle.locals.lookup (ofString "out") = some (.val (.word output)) := by
    rw [locals]; exact outLocal
  obtain ⟨result,post,tail,tailCost,tailRemaining,noTimeout⟩ :=
    evaluate_keccak_padded_tail_bounded middle pointer pad output stpMiddle padMiddle outMiddle
      outputAligned (postCode.trans code) (by omega)
  exact ⟨result,post,run.trans tail,by omega,by omega,noTimeout⟩

#print axioms evaluate_keccak_copy_tail_bounded_cells
end InitECandidate.Runtime
