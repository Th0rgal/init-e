import InitECandidate.Runtime.RlpItemDeclarationBound
import InitECandidate.Runtime.PanDecCallTerminal
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txFixedBytesArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16]]),
   .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])]

def txFixedBytesContinuation : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_tx_fixed_bytes with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_txFixedBytes_body : sourceFunctionBody Guest.guestFn_tx_fixed_bytes =
    .decCall (ofString "it") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
      txFixedBytesArguments txFixedBytesContinuation := by
  simp only [txFixedBytesArguments,txFixedBytesContinuation,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem txFixedBytes_continuation_straight : straightLine txFixedBytesContinuation = true := by
  simp only [txFixedBytesContinuation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_txFixedBytes_continuation : txFixedBytesContinuation =
    .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 0))
      (.raise (ofString "TxErr") (.const 15)) .skip)
      (.seq (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.var .local (ofString "width")))
        (.raise (ofString "TxErr") (.const 16)) .skip)
        (.return (.rfield 1 (.var .local (ofString "it"))))) := by
  simp only [txFixedBytesContinuation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_txFixedBytes_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)).1 ≠ none := by
  rw [source_txFixedBytes_body]
  apply evaluate_decCall_terminal
  intro current
  rw [source_txFixedBytes_continuation]
  apply evaluate_seq_terminal
  intro middle
  exact evaluate_seq_terminal middle _ _ (fun output => evaluate_return_terminal output _)

#print axioms evaluate_txFixedBytes_body_terminal

/-- Fixed-width field extraction adds only straight checks/return to the actual
RLP item call. The loaded slice interval remains an explicit memory premise. -/
theorem evaluate_txFixedBytes_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) txFixedBytesArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_txFixedBytes_body]
  exact evaluate_rlpItem_declaration_bounded state (ofString "it") txFixedBytesContinuation
    txFixedBytes_continuation_straight txFixedBytesArguments pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms evaluate_txFixedBytes_body_bounded
end InitECandidate.Runtime
