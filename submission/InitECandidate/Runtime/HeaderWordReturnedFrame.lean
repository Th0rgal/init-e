import InitECandidate.Runtime.HeaderWordBodyBound
import InitECandidate.Runtime.HeaderRlpFieldReturnedFrame
import InitECandidate.Runtime.HeaderNumericSuffixFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The complete original word-field helper retains all globals and old
memory above the parser scratch ceiling on actual successful returns. -/
theorem header_word_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_hdr_word_field) = (some (.returned v),post)) :
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ name : MlS, post.globals.lookup name = s.globals.lookup name) ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = s.memory address) := by
  have fullMetadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_hdr_word_field)
  rw [run] at fullMetadata
  rw [source_header_word_body] at run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "i"),.const 0] =
      some (headerRlpFieldValues .uint array index 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [headerRlpFieldValues,evalListHOLExact,evalHOLExact,atArray,atIndex]
  have lookup := header_rlp_field_lookup .uint array index 0
  simp only [headerRlpFieldName] at lookup
  rw [← code] at lookup
  let callState := callEntryStateHOLFinite s (headerRlpFieldCallee .uint array index 0)
  obtain ⟨value,bodyPost,ready,output,bodyRun,_,readyMemory,readyGlobals,_,_,_,readyCode,tail,restored⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope s post (ofString "f") (ofString "hdr_uint_field")
      (.comb [.one,.one]) (.comb [.one,.one]) _ _ (sourceFunctionBody (headerRlpFieldDeclaration .uint))
      (headerWordAt 1) (headerRlpFieldCallee .uint array index 0) v args lookup run
  have entryArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
  have lengthBound := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  have parserBound : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ callState.clock := by
    have product := Nat.mul_le_mul lengthBound (by omega : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLimit + 1) * 15 + 19)
    change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ s.clock - 1
    unfold headerRlpFieldCost at budget
    omega
  have parserFrame := header_rlp_field_returned_frame callState bodyPost .uint pointer length scratch frame ceiling inputLimit
    (eval_header_rlp_field_arguments callState array index pointer length input inputLength entryArray entryIndex calleeEntry)
    entry.noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena parserBound value bodyRun
  have suffixFrame := header_word_suffix_frame (setVarHOLFinite (ofString "f") value ready)
    (readyCode.trans (parserFrame.2.1.trans code))
  rw [tail] at suffixFrame
  have postMemory : post.memory = bodyPost.memory := by
    rw [restored]; exact suffixFrame.1.trans readyMemory
  have postGlobals : post.globals = bodyPost.globals := by
    rw [restored]; exact suffixFrame.2.trans readyGlobals
  refine ⟨fullMetadata.2.1,fullMetadata.1,?_,?_⟩
  · intro name
    rw [postGlobals]
    exact parserFrame.2.2.1 name
  · intro address above
    rw [postMemory]
    exact parserFrame.2.2.2 address above

#print axioms header_word_body_returned_frame
end InitECandidate.Runtime
