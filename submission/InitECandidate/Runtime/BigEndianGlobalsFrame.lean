import InitECandidate.Runtime.AddressFromWordsBound
import InitECandidate.Runtime.GuardedGlobalsFrame
import InitECandidate.Runtime.DiscardCallGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem storeBE32_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_st_be32) := by
  apply originalGlobalsFrame_leaf
  intro watched
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem bswap64_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_bswap64) := by
  apply originalGlobalsFrame_leaf
  intro watched
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Both the aligned byte-swap branch and the byte fallback keep every global,
including on invalid arguments, failed stores and exhausted clock. -/
theorem storeBE64_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_st_be64) := by
  have aligned : GuardedGlobalsFrame (fun _ => True) storeBE64AlignedBranch := by
    unfold storeBE64AlignedBranch
    apply GuardedGlobalsFrame.decCall _ _ _ _ originalRuntimeCode_bswap64_lookup
      (GuardedGlobalsFrame.of_original bswap64_body_globals_frame)
    apply GuardedGlobalsFrame.of_original
    exact originalGlobalsFrame_leaf storeBE64AlignedTail (fun _ => rfl)
  have guardFrame : OriginalGlobalsFrame storeBE64Guard := by
    unfold storeBE64Guard
    apply originalGlobalsFrame_conditional
    · intro F state code
      exact aligned state code trivial
    · exact originalGlobalsFrame_leaf _ (fun _ => rfl)
  have fallbackFrame : OriginalGlobalsFrame storeBE64Fallback := by
    unfold storeBE64Fallback
    apply originalGlobalsFrame_sequence
    · exact originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_storeBE32_lookup storeBE32_body_globals_frame _
    · apply originalGlobalsFrame_sequence
      · exact originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_storeBE32_lookup storeBE32_body_globals_frame _
      · exact originalGlobalsFrame_leaf _ (fun _ => rfl)
  rw [source_storeBE64_body]
  apply originalGlobalsFrame_sequence
  · exact guardFrame
  · exact fallbackFrame

theorem storeBE32_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "st_be32") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_storeBE32_lookup storeBE32_body_globals_frame arguments

theorem storeBE64_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "st_be64") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_storeBE64_lookup storeBE64_body_globals_frame arguments

theorem addressFromWords_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_addr_from_words) := by
  rw [source_addressFromWords_body]
  apply originalGlobalsFrame_sequence
  · exact storeBE32_call_globals_frame _
  · apply originalGlobalsFrame_sequence
    · exact storeBE64_call_globals_frame _
    · exact originalGlobalsFrame_sequence _ _ (storeBE64_call_globals_frame _)
        (originalGlobalsFrame_leaf _ (fun _ => rfl))

theorem addressFromWords_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "addr_from_words") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_addressFromWords_lookup addressFromWords_body_globals_frame arguments

#print axioms storeBE32_body_globals_frame
#print axioms bswap64_body_globals_frame
#print axioms storeBE64_body_globals_frame
#print axioms addressFromWords_body_globals_frame
#print axioms addressFromWords_call_globals_frame
end InitECandidate.Runtime
