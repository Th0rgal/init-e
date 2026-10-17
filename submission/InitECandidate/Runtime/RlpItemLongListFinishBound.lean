import InitECandidate.Runtime.RlpItemListPaths
import InitECandidate.Runtime.RlpItemLongFinish
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemLongListFinish : ProgHOL 64 :=
  match rlpItemLongList with
  | .dec _ _ _ (.seq _ (.decCall _ _ _ _ body)) => body
  | _ => .skip

def rlpItemLongListTail : ProgHOL 64 :=
  match rlpItemLongListFinish with
  | .seq _ (.seq _ tail) => tail
  | _ => .skip

theorem source_rlpItem_long_list_tail : rlpItemLongListTail =
    .seq (.call (some (none,none)) (ofString "rlp_list_count")
      [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
        .var .local (ofString "n")])
      (.return (.rstruct [.const 1,
        .op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
        .var .local (ofString "n"),
        .op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]])) := by
  simp only [rlpItemLongListTail,rlpItemLongListFinish,rlpItemLongList,rlpItemAfterLongString,
    rlpItemAfterShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItem_long_list_finish : rlpItemLongListFinish =
    rlpErrorChecks rlpItemLongChecks rlpItemLongListTail := by
  simp only [rlpItemLongListTail,rlpItemLongListFinish,rlpItemLongList,rlpItemAfterLongString,
    rlpItemAfterShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    rlpErrorChecks,rlpItemLongChecks,List.foldr,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_rlpItem_long_list_tail_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (argumentShape : arguments = [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
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
    let evaluated := evaluateHOLFiniteState state rlpItemLongListTail
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have bound := evaluate_rlpListCount_discard_call_bounded state arguments pointer length scratch frame ceiling inputLimit
    args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_rlpItem_long_list_tail]
  subst arguments
  exact evaluate_sequence_straight_bounded state _ _ _ bound (by decide)

#print axioms evaluate_rlpItem_long_list_tail_bounded
theorem evaluate_rlpItem_long_list_finish_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (argumentShape : arguments = [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
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
    let evaluated := evaluateHOLFiniteState state rlpItemLongListFinish
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have tail := evaluate_rlpItem_long_list_tail_bounded state arguments pointer length scratch frame ceiling inputLimit
    argumentShape args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  obtain ⟨result,post,run,cases⟩ := evaluate_rlp_error_checks state rlpItemLongChecks rlpItemLongListTail code (by omega)
  rw [source_rlpItem_long_list_finish,run]
  rcases cases with normal | terminal
  · rw [← normal]
    exact tail
  · obtain ⟨cost,remaining,noTimeout,_⟩ := terminal
    dsimp only
    exact ⟨by omega,remaining,noTimeout⟩

#print axioms evaluate_rlpItem_long_list_finish_bounded

/-- The original long-list finish cannot fall through even with malformed
locals, exhausted clock, or a rejecting nested list-count call. -/
theorem evaluate_rlpItem_long_list_finish_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpItemLongListFinish).1 ≠ none := by
  rw [source_rlpItem_long_list_finish]
  change (evaluateHOLFiniteState state (.seq _ (.seq _ rlpItemLongListTail))).1 ≠ none
  apply evaluate_seq_terminal
  intro middle
  apply evaluate_seq_terminal
  intro final
  rw [source_rlpItem_long_list_tail]
  apply evaluate_seq_terminal
  intro returned
  exact evaluate_return_terminal returned _

#print axioms evaluate_rlpItem_long_list_finish_terminal
end InitECandidate.Runtime
