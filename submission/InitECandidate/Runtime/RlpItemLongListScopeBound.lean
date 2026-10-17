import InitECandidate.Runtime.RlpItemLongListBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItem_long_list : rlpItemLongList =
    .dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"),.const 247]) rlpItemLongListBody := by
  simp only [rlpItemLongListBody,rlpItemLongList,rlpItemAfterLongString,
    rlpItemAfterShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_rlpItem_long_list_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : (header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemLongList
    state.clock ≤ evaluated.2.clock + ((header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  have bound := evaluate_rlpItem_long_list_body_bounded entered pointer total (header - 247) scratch frame ceiling inputLimit
    atPointer atLength atTotal inputRange nonzero lengthBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena ticks
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_long_list,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemLongListBody; _) ∧ _
  cases run : evaluateHOLFiniteState entered rlpItemLongListBody with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpItem_long_list_bounded
end InitECandidate.Runtime
