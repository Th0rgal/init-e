import InitECandidate.Runtime.RlpItemLongDispatchBound
import InitECandidate.Runtime.RlpListCountDiscardBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemShortList : ProgHOL 64 :=
  match rlpItemAfterLongString with
  | .seq (.ite _ body _) _ => body
  | _ => .skip

def rlpItemLongList : ProgHOL 64 :=
  match rlpItemAfterLongString with
  | .seq _ body => body
  | _ => .skip

def rlpItemShortListTail : ProgHOL 64 :=
  match rlpItemShortList with
  | .dec _ _ _ (.seq _ tail) => tail
  | _ => .skip

theorem source_rlpItem_list_dispatch : rlpItemAfterLongString =
    .seq (.ite (.cmp .notLower (.const 247) (.var .local (ofString "b")))
      rlpItemShortList .skip) rlpItemLongList := by
  simp only [rlpItemAfterLongString,rlpItemShortList,rlpItemLongList,rlpItemAfterShortString,
    rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItem_short_list_tail : rlpItemShortListTail =
    .seq (.call (some (none,none)) (ofString "rlp_list_count")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")])
      (.return (.rstruct [.const 1,
        .op .add [.var .local (ofString "p"),.const 1],
        .var .local (ofString "n"),.op .add [.const 1,.var .local (ofString "n")]])) := by
  simp only [rlpItemShortListTail,rlpItemShortList,rlpItemAfterLongString,rlpItemAfterShortString,
    rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_rlpItem_short_list_tail_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (argumentShape : arguments = [.op .add [.var .local (ofString "p"),.const 1],
      .var .local (ofString "n")])
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemShortListTail
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_rlpListCount_discard_call_bounded state arguments pointer length scratch frame ceiling inputLimit
    args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_rlpItem_short_list_tail]
  subst arguments
  exact evaluate_sequence_straight_bounded state _ _ _ bound (by decide)

#print axioms evaluate_rlpItem_short_list_tail_bounded
end InitECandidate.Runtime
