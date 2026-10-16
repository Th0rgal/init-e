import InitECandidate.Runtime.PanFunctionRenameClock
import InitECandidate.Runtime.ZeroGlobalsFrame
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- The generated initializer leaves the initial empty locals intact. -/
theorem canonical_initialized_globals_locals (input : Guest.InputBlob) :
    (canonicalInitializedGlobals input).locals = HolFiniteMapExact.empty :=
  (Classical.choose_spec (canonical_globals_ready input)).2.2.2.2.1

/-- The unrenamed source carrier uses exactly the original source runtime
fields, with the initialized globals and original function table installed. -/
theorem canonical_unrenamed_source_fields (input : Guest.InputBlob) :
    canonicalUnrenamedSourceEntry input =
      {sourceInitialState input with
        globals := baselineGlobalNames.foldl
          (fun globals name => globals.update (name,.val (.word 0))) HolFiniteMapExact.empty
        eshapes := (canonicalPanEntryState input).eshapes
        code := HolFiniteMapExact.empty.updateList
          (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse} := by
  unfold canonicalUnrenamedSourceEntry sourceEntryCode
  rw [zero_global_post_frame,canonical_initialized_globals_locals]
  rfl

#print axioms canonical_initialized_globals_locals
#print axioms canonical_unrenamed_source_fields
end InitECandidate.Runtime
