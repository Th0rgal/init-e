import InitECandidate.Runtime.BaselineSourceFunctionsSetup
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The original function declaration evaluator installs precisely the
original-named source entry used by the quantitative native simulation. -/
theorem canonical_source_functions_evaluate (input : Guest.InputBlob) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      (zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames)
      (fun address => Classical.propDecidable
        ((zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames).memaddrs address))
      FrontendStages.Declarations.functionDeclarations = some (canonicalUnrenamedSourceEntry input) := by
  classical
  let state := zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames
  have structs : state.structs = [] := by
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have code : state.code = HolFiniteMapExact.empty := by
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have locals : state.locals = (canonicalInitializedGlobals input).locals := by
    rw [canonical_initialized_globals_locals]
    dsimp only [state]
    rw [zero_global_post_frame]
    rfl
  have checked : panDeclarationSetup state.structs state.eshapes
      FrontendStages.Declarations.functionDeclarations = true := by
    rw [structs,pan_function_setup_exceptions _ [] state.eshapes HolFiniteMapExact.empty baseline_source_functions_kind]
    exact baseline_source_functions_setup
  have evaluated := panDeclarationSetup_evaluates FrontendStages.Declarations.functionDeclarations state checked
  rw [baseline_source_functions_exceptions] at evaluated
  change evaluateDeclsHOLFinite state FrontendStages.Declarations.functionDeclarations =
    some {state with code := state.code.updateList (functionsHOL FrontendStages.Declarations.functionDeclarations)} at evaluated
  rw [code,function_table_reverse _ baseline_source_functions_distinct] at evaluated
  have post : {state with code := (HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)} =
      canonicalUnrenamedSourceEntry input := by
    exact (source_entry_code_same_locals state _).symm.trans
      (congrArg (fun initialLocals => sourceEntryCode state initialLocals
        (HolFiniteMapExact.empty.updateList
          (functionsHOL FrontendStages.Declarations.functionDeclarations).reverse)) locals)
  rw [post] at evaluated
  exact evaluated

#print axioms canonical_source_functions_evaluate
end InitECandidate.Runtime
