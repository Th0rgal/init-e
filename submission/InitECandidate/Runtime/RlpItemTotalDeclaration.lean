import InitECandidate.Runtime.OriginalRlpItemTotalCode
import InitECandidate.Runtime.RlpItemTotalBodyProgress
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original item-total declaration binds a positive
input-bounded word and executes its continuation with caller locals restored. -/
theorem evaluate_rlpItemTotal_declaration_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) (ticks : 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_item_total") arguments continuation) = (none,post)) :
    ∃ (consumed : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word consumed)) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_item_total") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_total,.one) := by
    rw [code]; exact originalRuntimeCode_rlpItemTotal_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_total") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item_total) .one pointer length (by decide) installed
  let property := fun value : ValueHOL 64 => ∃ consumed : BitVec 64,
    value = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ length.toNat
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_item_total) =
      (some (.returned value),output) → property value := by
    intro value output evaluated
    exact rlpItemTotal_body_progress entry output pointer length value pointerLocal lengthLocal code
      (by change 12 ≤ state.clock - 1; omega) evaluated
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_return_property state post name
    (ofString "rlp_item_total") .one .one arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_item_total) continuation callee args lookup property bodyProperty run
  obtain ⟨consumed,shape,positive,bounded⟩ := valid
  subst value
  exact ⟨consumed,ready,output,positive,bounded,locals,tail,restored⟩

#print axioms evaluate_rlpItemTotal_declaration_progress
end InitECandidate.Runtime
