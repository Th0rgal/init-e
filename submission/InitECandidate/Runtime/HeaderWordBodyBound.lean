import InitECandidate.Runtime.HeaderUintReturned
import InitECandidate.Runtime.HeaderWordSuffixBound
import InitECandidate.Runtime.HeaderRlpFieldCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_header_word_body : sourceFunctionBody Guest.guestFn_hdr_word_field =
    .decCall (ofString "f") (.comb [.one,.one]) (ofString "hdr_uint_field")
      [.var .local (ofString "arr"),.var .local (ofString "i"),.const 0] (headerWordAt 1) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original word-field decoder composes its actual unsigned
parser with the size guard and eight-byte accumulation suffix. -/
theorem runBounded_header_word_body {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : headerRlpFieldCost inputLimit + 9 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_hdr_word_field) (headerRlpFieldCost inputLimit + 9) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "i"),.const 0] =
      some (headerRlpFieldValues .uint array index 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [headerRlpFieldValues,evalListHOLExact,evalHOLExact,atArray,atIndex]
  rw [source_header_word_body]
  change RunBounded s _ (headerRlpFieldCost inputLimit + 1 + 8)
  apply RunBounded.decCall (bodyCost := headerRlpFieldCost inputLimit) (tailCost := 8) args (by omega)
  intro body callee shape lookup
  have installedLookup := header_rlp_field_lookup .uint array index 0
  simp only [headerRlpFieldName] at installedLookup
  rw [code,installedLookup] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj lookup
  let entryState := callEntryStateHOLFinite s (headerRlpFieldCallee .uint array index 0)
  have entryArray : entryState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp (config := {decide := true}) [entryState,callEntryStateHOLFinite,headerRlpFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryIndex : entryState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp (config := {decide := true}) [entryState,callEntryStateHOLFinite,headerRlpFieldCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry entryState array index pointer length input inputLength :=
    entry.after_frame s entryState _ _ _ _ _ _ rfl rfl rfl
  refine ⟨runBounded_header_rlp_field_input entryState .uint array index pointer length input inputLength scratch frame
    ceiling inputLimit entryArray entryIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena (by change headerRlpFieldCost inputLimit ≤ s.clock - 1; omega),?_⟩
  intro value post returned ticks
  change evaluateHOLFiniteState entryState (sourceFunctionBody Guest.guestFn_hdr_uint_field) = _ at returned
  have lengthBound := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  obtain ⟨outputPointer,outputLength,valueEq,_,_,_,_⟩ := header_uint_body_returned entryState post pointer length value
    (eval_header_rlp_field_arguments entryState array index pointer length input inputLength entryArray entryIndex calleeEntry)
    code entry.noWrap (by omega) (by change 12 ≤ s.clock - 1; unfold headerRlpFieldCost at budget; omega) returned
  have installed := evaluateHOLFiniteState_metadata entryState (sourceFunctionBody Guest.guestFn_hdr_uint_field)
  rw [returned] at installed
  exact runBounded_header_word_suffix (setVarHOLFinite (ofString "f") value {post with locals := s.locals})
    outputPointer outputLength (installed.1.trans code)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,valueEq]) ticks

#print axioms source_header_word_body
#print axioms runBounded_header_word_body
end InitECandidate.Runtime
