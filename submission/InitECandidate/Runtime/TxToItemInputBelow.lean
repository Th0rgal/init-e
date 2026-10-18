import InitECandidate.Runtime.RlpSliceInputArguments
import InitECandidate.Runtime.TxToItemBodyBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful extraction from the input-bounded slice prefix retains runtime globals. -/
theorem txToItem_input_returned_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_to_item) = (some (.returned value),post)) (address : BitVec 64) (below : address.toNat < frame.toNat) :
    post.memory address = state.memory address := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,_,_⟩ := rlpSliceInputPrefix_fixed_bytes_arguments state
    array index input inputLength filled arrayLocal indexLocal valid inside
  have factor : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLength.toNat + 1) * 15 + 19 := by omega
  have cost := Nat.mul_le_mul lengthBound factor
  exact txToItem_body_returned_below state post pointer length scratch frame ceiling inputLimit args noWrap
    (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) value run address below

#print axioms txToItem_input_returned_below
end InitECandidate.Runtime
