import InitECandidate.Runtime.RlpSliceInputArguments
import InitECandidate.Runtime.TxScalarWordBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The input-bounded prefix supplies the real scalar-word argument loads and
bounds every extraction by the common original input length. -/
theorem evaluate_txScalarWord_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index maximum input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (maxLocal : state.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_word)
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92642) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entry := callEntryStateHOLFinite state (txScalarWordCallee array index maximum)
  have arr : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have idx : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have retained : RlpSliceInputPrefix entry array input inputLength filled := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  obtain ⟨pointer,length,args,noWrap,lengthBound,_,_⟩ := rlpSliceInputPrefix_fixed_bytes_arguments entry
    array index input inputLength filled arr idx retained inside
  have factor : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLength.toNat + 1) * 15 + 19 := by omega
  have cost := Nat.mul_le_mul lengthBound factor
  have bounded := evaluate_txScalarWord_body_bounded state array index maximum pointer length scratch frame ceiling inputLimit
    arrayLocal indexLocal maxLocal args noWrap
    (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  refine ⟨?_,bounded.2.1,bounded.2.2⟩
  exact Nat.le_trans bounded.1 (Nat.add_le_add_left (Nat.add_le_add_right cost 92642) _)

#print axioms evaluate_txScalarWord_input_bounded
end InitECandidate.Runtime
