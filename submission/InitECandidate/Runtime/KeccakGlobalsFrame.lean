import InitECandidate.Runtime.DiscardCallGlobalsFrame
import InitECandidate.Runtime.OriginalMemzeroCode
import InitECandidate.Runtime.OriginalMemcpyCode
import InitECandidate.Runtime.OriginalKeccakFCode
import InitECandidate.Runtime.OriginalKeccakAbsorbCode
import InitECandidate.Runtime.OriginalKeccakCode
import InitECandidate.Runtime.KeccakFBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem memzero_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_memzero) := by
  apply originalGlobalsFrame_leaf
  intro watched
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem memcpy_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_memcpy) := by
  apply originalGlobalsFrame_leaf
  intro watched
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem memzero_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "memzero") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_memzero_lookup memzero_body_globals_frame arguments

theorem memcpy_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "memcpy") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_memcpy_lookup memcpy_body_globals_frame arguments

theorem keccakF_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_keccak_f1600) := by
  rw [source_keccakF1600_body]
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_external _ _ _ _ _
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem keccakF_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "keccak_f1600") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_keccakF1600_lookup keccakF_body_globals_frame arguments

theorem keccakAbsorb_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_keccak_absorb_block) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply originalGlobalsFrame_declaration
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · apply originalGlobalsFrame_sequence
    · exact keccakF_call_globals_frame _
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem keccakAbsorb_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "keccak_absorb_block") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_keccakAbsorb_lookup keccakAbsorb_body_globals_frame arguments

/-- The full Keccak implementation and all its callees retain allocator,
scratch and decoder globals, at every fuel and for every external outcome. -/
theorem keccak_body_globals_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_keccak256) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_while
    | apply originalGlobalsFrame_conditional
    | exact memzero_call_globals_frame _
    | exact memcpy_call_globals_frame _
    | exact keccakAbsorb_call_globals_frame _

theorem keccak_call_globals_frame (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "keccak256") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_keccak_lookup keccak_body_globals_frame arguments

#print axioms memzero_body_globals_frame
#print axioms memcpy_body_globals_frame
#print axioms keccakF_call_globals_frame
#print axioms keccakAbsorb_call_globals_frame
#print axioms keccak_body_globals_frame
#print axioms keccak_call_globals_frame
end InitECandidate.Runtime
