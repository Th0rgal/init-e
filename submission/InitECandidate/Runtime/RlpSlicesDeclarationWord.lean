import InitECandidate.Runtime.RlpSlicesBodyResult
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.PanDecCallNormalCheckedProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal slice-builder declarations bind an input-bounded count and restore
caller locals before the actual continuation. -/
theorem evaluate_rlpSlices_declaration_word_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "rlp_list_to_slices") arguments continuation) = (none,post)) :
    ∃ (array count : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      count.toNat ≤ length.toNat ∧ ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word array),.val (.word count)]) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  let property := fun value : ValueHOL 64 => ∃ (array count : BitVec 64),
    value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ length.toNat
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) =
      (some (.returned value),output) →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true → property value := by
    intro value output evaluated checked _
    obtain ⟨array,count,returned,bounded⟩ := rlpSlices_body_returned_contract entry output pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1; omega) value evaluated
    subst value
    cases array with
    | val atom => cases atom with
      | word pointer => exact ⟨pointer,count,rfl,bounded⟩
    | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at checked
    | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at checked
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_checked_property state post name
    (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) continuation callee args lookup property bodyProperty run
  obtain ⟨array,count,shape,bounded⟩ := valid
  subst value
  exact ⟨array,count,ready,output,bounded,locals,tail,restored⟩

#print axioms evaluate_rlpSlices_declaration_word_progress
end InitECandidate.Runtime
