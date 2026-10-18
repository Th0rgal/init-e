import InitECandidate.Runtime.TxBytesItemInputBound
import InitECandidate.Runtime.OriginalTxBytesItemCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original fixed-byte calls with straight continuations inherit the common
input budget from their concrete slice prefix. -/
theorem evaluate_txBytesItem_declaration_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (supported : straightLine continuation = true)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index)])
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "tx_bytes_item") arguments continuation)
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength filled := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have bound := evaluate_txBytesItem_input_bounded entry array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_bytes_item) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "tx_bytes_item") =
        some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_bytes_item,.comb [.one,.one]) := by
      rw [code]; exact originalRuntimeCode_txBytesItem_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_bytes_item") (ofString "arr") (ofString "i")
      (sourceFunctionBody Guest.guestFn_tx_bytes_item) (.comb [.one,.one]) array index (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact evaluate_decCall_straight_bounded state bodyPost name (ofString "tx_bytes_item") (.comb [.one,.one]) (.comb [.one,.one]) arguments
      [.val (.word array),.val (.word index)] (sourceFunctionBody Guest.guestFn_tx_bytes_item) continuation callee bodyResult
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) args lookup (by omega) bodyRun bound.2.1
      (by omega) bound.2.2 supported

#print axioms evaluate_txBytesItem_declaration_input_bounded
end InitECandidate.Runtime
