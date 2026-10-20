import InitECandidate.Runtime.DiscardCallGlobalsFrame
import InitECandidate.Runtime.OriginalKeyToNibblesCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem key_nibble_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_key_to_nibbles) := by
 apply originalGlobalsFrame_leaf
 intro watched
 unfold sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem key_nibble_call_globals_frame (arguments : List (ExpHOL 64)) :
 OriginalGlobalsFrame (.call (some (none,none)) (ofString "key_to_nibbles") arguments) :=
 originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_keyToNibbles_lookup key_nibble_body_globals_frame arguments

#print axioms key_nibble_call_globals_frame
end InitECandidate.Runtime
