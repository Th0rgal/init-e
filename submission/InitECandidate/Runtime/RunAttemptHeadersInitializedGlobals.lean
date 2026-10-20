import InitECandidate.Runtime.HeadersInitializerGlobalClosure
import InitECandidate.Runtime.RunAttemptHeadersToParentReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Protected world initialization globals survive the actual returned header call. -/
theorem RunAttemptHeaderValidationFacts.initializer_global {F : Type}
 (s ready : PanSemStateFiniteExact 64 F)
 (si array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64) (ceiling : Nat)
 (facts : RunAttemptHeaderValidationFacts s ready si array count input inputLength scratch frame heap keccakState keccakPad ceiling)
 (code : s.code=originalRuntimeCode) (key : MlS) (member : key∈headersInitializerGlobals) :
 ready.globals.lookup key=s.globals.lookup key := by
 obtain ⟨value,bodyPost,run,locals,memory,globals,rest⟩ := facts
 have kept := evaluate_headers_initializer_global (callEntryStateHOLFinite s (validateHeadersCallee array count))
  (sourceFunctionBody Guest.guestFn_validate_headers) key member
  (headers_initializer_global_installed originalRuntimeCode_validateHeaders_lookup (by decide) member) code
 rw [run] at kept
 rw [globals]
 exact kept
#print axioms RunAttemptHeaderValidationFacts.initializer_global
end InitECandidate.Runtime
