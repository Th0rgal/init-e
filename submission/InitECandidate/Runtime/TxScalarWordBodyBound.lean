import InitECandidate.Runtime.TxScalarItemBodyBound
import InitECandidate.Runtime.OriginalTxScalarItemCode
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.TwoWordValueShape
import InitECandidate.Runtime.TxScalarWordAfterFieldBound
import InitECandidate.Runtime.BlobHashesDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txScalarWordCallee (array index maximum : BitVec 64) :=
  ((HolFiniteMapExact.empty.update (ofString "arr",ValueHOL.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "maxb",.val (.word maximum))

theorem source_txScalarWord_body : sourceFunctionBody Guest.guestFn_tx_scalar_word =
    .decCall (ofString "f") (.comb [.one,.one]) (ofString "tx_scalar_item")
      [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")]
      txScalarWordAfterField := by
  simp only [txScalarWordAfterField,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Complete scalar-word extraction, including its field parser and guarded
conversion. The loaded slice is an explicit memory premise. -/
theorem evaluate_txScalarWord_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index maximum pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (maxLocal : state.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (args : evalListHOLFinite (callEntryStateHOLFinite state (txScalarWordCallee array index maximum))
      (h := fun address => Classical.propDecidable (state.memaddrs address)) txScalarItemArguments =
        some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92642 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_word)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92642) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := txScalarWordCallee array index maximum
  let entry := callEntryStateHOLFinite state callee
  let cost := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633
  have bodyBudget : cost ≤ entry.clock := by
    change cost ≤ state.clock - 1
    dsimp only [cost]
    omega
  have bound := evaluate_txScalarItem_body_bounded entry pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  have passedArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")] =
      some [.val (.word array),.val (.word index),.val (.word maximum)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,maxLocal]
  have installed := originalRuntimeCode_txScalarItem_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_item")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_item)
    (.comb [.one,.one]) array index maximum (by decide) (by decide) (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_scalar_item) with
  | mk result post =>
    rw [bodyRun] at bound
    dsimp only at bound
    have positive : 0 < state.clock := by omega
    have bodyCost : state.clock - 1 ≤ post.clock + cost := bound.1
    have tailBudget : 8 ≤ post.clock := by
      have total : cost + 1 + 8 ≤ state.clock := by dsimp only [cost]; omega
      omega
    rw [source_txScalarWord_body]
    have composed := evaluate_decCall_checked_continuation_bounded state post (ofString "f")
      (ofString "tx_scalar_item") (.comb [.one,.one]) (.comb [.one,.one])
      [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")]
      [.val (.word array),.val (.word index),.val (.word maximum)]
      (sourceFunctionBody Guest.guestFn_tx_scalar_item) txScalarWordAfterField callee result (cost + 1) 8
      passedArgs lookup (Nat.ne_of_gt positive) bodyRun bound.2.1
      (blobHashes_call_clock_bound _ _ _ positive bodyCost) bound.2.2 ?_
    · simpa only [cost,Nat.add_assoc] using composed
    · intro value returned checked
      have checkedOne : shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true := by
        simpa only [Bool.and_self] using checked
      obtain ⟨p,n,rfl⟩ := value_two_words_of_checked_shape value checkedOne
      let resumed := setVarHOLFinite (ofString "f") (.rStruct [.val (.word p),.val (.word n)])
        {post with locals := state.locals}
      have fieldLocal : resumed.locals.lookup (ofString "f") =
          some (.rStruct [.val (.word p),.val (.word n)]) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have tail := evaluate_txScalarWord_after_field_bounded resumed p n fieldLocal tailBudget
      exact ⟨tail.1,tail.2.1,tail.2.2.1⟩

#print axioms evaluate_txScalarWord_body_bounded
end InitECandidate.Runtime
