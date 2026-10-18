import InitECandidate.Runtime.RlpItemDeclarationBound
import InitECandidate.Runtime.PanDecCallTerminal
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txToItemArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16]]),
   .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])]

def txToItemContinuation : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_tx_to_item with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_txToItem_body : sourceFunctionBody Guest.guestFn_tx_to_item =
    .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
      txToItemArguments txToItemContinuation := by
  simp only [txToItemArguments,txToItemContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem txToItem_continuation_straight : straightLine txToItemContinuation = true := by
  simp only [txToItemContinuation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Transaction field extraction adds only straight checks/return to the actual
RLP item call. The loaded slice interval remains an explicit memory premise. -/
theorem evaluate_txToItem_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) txToItemArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_to_item)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_txToItem_body]
  exact evaluate_rlpItem_declaration_bounded state (ofString "it") txToItemContinuation
    txToItem_continuation_straight txToItemArguments pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms evaluate_txToItem_body_bounded
end InitECandidate.Runtime
