import InitECandidate.Runtime.Sha256GlobalsFrame
import InitECandidate.Runtime.MixInLengthBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem storeLE32_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_st_le32) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional

theorem storeLE32_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "st_le32") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ vmLookup_st_le32 storeLE32_body_globals_frame arguments

#print axioms storeLE32_body_globals_frame
#print axioms storeLE32_call_globals_frame

theorem storeLE64_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_st_le64) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact storeLE32_call_globals_frame _

theorem storeLE64_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "st_le64") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ vmLookup_st_le64 storeLE64_body_globals_frame arguments

#print axioms storeLE64_body_globals_frame
#print axioms storeLE64_call_globals_frame

theorem mixInLength_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_mix_in_length) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact memzero_call_globals_frame _
    | exact storeLE64_call_globals_frame _
    | exact shaPair_call_globals_frame _

theorem mixInLength_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "mix_in_length") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_mixInLength_lookup mixInLength_body_globals_frame arguments

#print axioms mixInLength_body_globals_frame
#print axioms mixInLength_call_globals_frame

end InitECandidate.Runtime
