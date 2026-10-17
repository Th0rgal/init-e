import InitECandidate.Runtime.RlpItemListPaths
import InitECandidate.Runtime.RlpItemShortBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemShortListBody : ProgHOL 64 :=
  match rlpItemShortList with
  | .dec _ _ _ body => body
  | _ => .skip

theorem source_rlpItem_short_list_body : rlpItemShortListBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1])
      (.var .local (ofString "n")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
      rlpItemShortListTail := by
  simp only [rlpItemShortListBody,rlpItemShortListTail,rlpItemShortList,rlpItemAfterLongString,
    rlpItemAfterShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original short-list length check either rejects within one call tick
or reaches the proved count-and-return bound without changing state. -/
theorem evaluate_rlpItem_short_list_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    let evaluated := evaluateHOLFiniteState state rlpItemShortListBody
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have tail := evaluate_rlpItem_short_list_tail_bounded state arguments pointer length scratch frame ceiling inputLimit
    argumentShape args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_⟩ := evaluate_rlp_error_check state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n")))
    3 code (by omega)
  rw [source_rlpItem_short_list_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact tail
  | some stopped =>
    dsimp only
    exact ⟨by omega,remaining,noTimeout⟩

#print axioms evaluate_rlpItem_short_list_body_bounded
theorem evaluate_rlpItem_short_list_typed_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (noWrap : (pointer + 1).toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemShortListBody
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  apply evaluate_rlpItem_short_list_body_bounded state
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")]
    (pointer + 1) length scratch frame ceiling inputLimit rfl
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord])
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms evaluate_rlpItem_short_list_typed_body_bounded
end InitECandidate.Runtime
