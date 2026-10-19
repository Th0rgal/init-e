import InitECandidate.Runtime.CompactNibbleAfterAlloc
import InitECandidate.Runtime.OriginalKeyToNibblesCode
import InitECandidate.Runtime.LookupCodeInstalledBody
import InitECandidate.Runtime.EvGlobalKeep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keyNibbleOnlyGood (function : MlS) : Bool := decide (function = ofString "key_to_nibbles")

theorem key_nibble_body_keeps_global (watched : MlS) :
    keepsG watched keyNibbleOnlyGood (sourceFunctionBody Guest.guestFn_key_to_nibbles) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem key_nibble_only_global_closure (watched : MlS) :
    ∀ function, keyNibbleOnlyGood function = true → ∀ values body callee returnShape,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,returnShape) →
      keepsG watched keyNibbleOnlyGood body = true := by
  intro function good values body callee returnShape lookup
  have same : function = ofString "key_to_nibbles" := by simpa [keyNibbleOnlyGood] using good
  subst function
  have sameBody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "key_to_nibbles")
    [(ofString "key",.one),(ofString "n",.one),(ofString "out",.one)]
    (sourceFunctionBody Guest.guestFn_key_to_nibbles) body .one returnShape values callee
    originalRuntimeCode_keyToNibbles_lookup lookup
  subst body
  exact key_nibble_body_keeps_global watched

theorem compact_after_alloc_global_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s compactNibbleAfterAlloc).2.globals = s.globals := by
  apply HolFiniteMapExact.ext
  funext watched
  apply evaluate_keepsG watched keyNibbleOnlyGood (key_nibble_only_global_closure watched)
  · simp only [source_compactNibble_after_alloc,source_compactNibble_prefix,
      source_compactNibble_finish,source_compactNibble_conversion]
    rfl
  · exact code

#print axioms key_nibble_body_keeps_global
#print axioms key_nibble_only_global_closure
#print axioms compact_after_alloc_global_frame
end InitECandidate.Runtime
