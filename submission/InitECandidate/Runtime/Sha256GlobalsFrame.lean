import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.BigEndianGlobalsFrame
import InitECandidate.Runtime.Sha256PairBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem shaStateInit_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_sha256_state_init) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact originalGlobalsFrame_external _ _ _ _ _

theorem shaStateInit_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "sha256_state_init") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ vmLookup_sha256_state_init shaStateInit_body_globals_frame arguments

#print axioms shaStateInit_body_globals_frame
#print axioms shaStateInit_call_globals_frame

theorem shaBlock_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_sha256_block) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact originalGlobalsFrame_external _ _ _ _ _
    | exact memcpy_call_globals_frame _

theorem shaBlock_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "sha256_block") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_sha256Block_lookup shaBlock_body_globals_frame arguments

#print axioms shaBlock_body_globals_frame
#print axioms shaBlock_call_globals_frame

theorem shaFinish_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_sha256_finish) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact originalGlobalsFrame_external _ _ _ _ _
    | exact storeBE32_call_globals_frame _

theorem shaFinish_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "sha256_finish") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ vmLookup_sha256_finish shaFinish_body_globals_frame arguments

#print axioms shaFinish_body_globals_frame
#print axioms shaFinish_call_globals_frame

theorem shaPair_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_sha256_pair) := by
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact originalGlobalsFrame_external _ _ _ _ _
    | exact shaStateInit_call_globals_frame _
    | exact memcpy_call_globals_frame _
    | exact shaBlock_call_globals_frame _
    | exact memzero_call_globals_frame _
    | exact storeBE64_call_globals_frame _
    | exact shaFinish_call_globals_frame _

theorem shaPair_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "sha256_pair") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_sha256Pair_lookup shaPair_body_globals_frame arguments

#print axioms shaPair_body_globals_frame
#print axioms shaPair_call_globals_frame

end InitECandidate.Runtime
