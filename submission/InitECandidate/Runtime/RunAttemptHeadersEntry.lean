import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.OriginalValidateHeadersCode
import InitECandidate.Runtime.PanTwoWordResultLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def validateHeadersCallee (array count : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "n",.val (.word count))

/-- Original code lookup supplies the actual two-word header-validation
callee and its pair return shape. -/
theorem lookup_validate_headers_callee (array count : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "validate_headers") [.val (.word array),.val (.word count)] =
      some (sourceFunctionBody Guest.guestFn_validate_headers,validateHeadersCallee array count,.comb [.one,.one]) :=
  pan_two_word_result_lookup _ _ _ _ _ array count _ (by decide) originalRuntimeCode_validateHeaders_lookup

/-- The caller's linked witness is preserved on real call entry, with the
original source parameters bound to the decoded array and count. -/
theorem run_attempt_headers_entry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si array count input length heap : BitVec 64)
    (linked : WitnessArrayLinked s si 72 80 array count input length heap) :
    let entry := callEntryStateHOLFinite s (validateHeadersCallee array count)
    entry.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
    entry.locals.lookup (ofString "n") = some (.val (.word count)) ∧
    RlpSliceInputPrefix entry array input length count.toNat ∧
    array.toNat + count.toNat * 16 ≤ heap.toNat ∧ count.toNat ≤ length.toNat / 4 := by
  dsimp only
  refine ⟨?_,?_,?_,linked.arrayEnd,linked.countBound⟩
  · simp (config := {decide := true}) [callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [callEntryStateHOLFinite,validateHeadersCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro slot inside
    obtain ⟨pointer,size,entry⟩ := linked.slices slot inside
    exact ⟨pointer,size,entry.after_frame s _ array slot pointer size input length rfl rfl rfl⟩

#print axioms lookup_validate_headers_callee
#print axioms run_attempt_headers_entry
end InitECandidate.Runtime
