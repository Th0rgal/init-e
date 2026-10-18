import InitECandidate.Runtime.OriginalHtrU64AtCode
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.MerkleizeSource
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem htrU64At_funBounded : FunBounded (ofString "htr_u64_at") 29 :=
  ⟨_,_,_,originalRuntimeCode_htrU64At_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

theorem htrU64At_body_globals : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_htr_u64_at) := by
  rw [sourceFunctionBody_eq_structural]
  exact originalGlobalsFrame_sequence _ _ (memzero_call_globals_frame _)
    (originalGlobalsFrame_sequence _ _ (memcpy_call_globals_frame _) (originalGlobalsFrame_leaf _ (by intro watched; rfl)))

theorem htrU64At_call_globals (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) (ofString "htr_u64_at") arguments) :=
  originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_htrU64At_lookup htrU64At_body_globals arguments

#print axioms htrU64At_funBounded
#print axioms htrU64At_body_globals
#print axioms htrU64At_call_globals
end InitECandidate.Runtime
