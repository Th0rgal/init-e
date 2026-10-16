import InitECandidate.Runtime.CanonicalSourceEntryFields
import InitECandidate.Runtime.PanFunctionDeclarationSetup
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

theorem baseline_source_functions_kind :
    FrontendStages.Declarations.functionDeclarations.all isFunctionHOL = true := by decide_cbv

theorem baseline_source_functions_setup :
    panDeclarationSetup [] HolFiniteMapExact.empty FrontendStages.Declarations.functionDeclarations = true := by decide_cbv

theorem baseline_source_functions_exceptions :
    exceptionsHOL FrontendStages.Declarations.functionDeclarations = [] := by kernel_rfl

theorem baseline_source_functions_distinct :
    ((functionsHOL FrontendStages.Declarations.functionDeclarations).map Prod.fst).Nodup := by
  have compiled := baseline_pan_distinct
  rw [baseline_global_function_table,List.map_cons,List.nodup_cons] at compiled
  have renamed : ((functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations).map Prod.fst).Nodup := by
    simpa only [compileFunctionEntries,List.map_map,Function.comp_def] using compiled.2
  have names : (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations).map Prod.fst =
      ((functionsHOL FrontendStages.Declarations.functionDeclarations).map Prod.fst).map
        (fpermName FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart) := by
    rw [show FrontendStages.Declarations.renamedFunctionDeclarations =
      fpermDecsHOL FrontendStages.Declarations.globalStart FrontendStages.Declarations.globalNewStart
        FrontendStages.Declarations.functionDeclarations from (GlobalsComputation.fpermDecs_eq_map _ _ _).symm]
    rw [functionsFpermDecsHOL]
    simp only [List.map_map]
    rfl
  rw [names] at renamed
  exact List.Nodup.of_map _ renamed

#print axioms baseline_source_functions_kind
#print axioms baseline_source_functions_setup
#print axioms baseline_source_functions_exceptions
#print axioms baseline_source_functions_distinct
end InitECandidate.Runtime
