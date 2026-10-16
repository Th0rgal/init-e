import InitECandidate.Runtime.CanonicalGlobalsReady
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

def compileFunctionEntries {width : Nat} [NeZero width] (context : PanGlobalsContextExact width)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :=
  entries.map (fun entry => (entry.1,entry.2.1,compileProgExactHOL context entry.2.2.1,entry.2.2.2))

/-- Extracting the function table commutes with body compilation. -/
theorem functions_map_compile {width : Nat} [NeZero width] (context : PanGlobalsContextExact width)
    (declarations : List (DeclHOL width)) :
    functionsHOL (declarations.map (fun declaration => match declaration with
      | .function fn => .function {fn with body := compileProgExactHOL context fn.body}
      | _ => .name (Basis.Pure.MlString.ofString "") [])) =
      compileFunctionEntries context (functionsHOL declarations) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
    cases declaration <;> simp only [List.map_cons,functionsHOL,compileFunctionEntries,List.map_cons] at ih ⊢ <;>
      rw [ih]

theorem baseline_renamed_functions_kind :
    FrontendStages.Declarations.renamedFunctionDeclarations.all isFunctionHOL = true := by decide_cbv

/-- The actual global-lowered function table compiles the renamed original
bodies with the final context produced by all 93 global declarations. -/
theorem baseline_compiled_functions :
    functionsHOL FrontendStages.Declarations.translatedFunctions =
      compileFunctionEntries FrontendStages.Declarations.globalContext
        (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) := by
  have compiled := PanGlobalsCompileDecsStructural.compile_decs_functions_thmHOL
    FrontendStages.Declarations.globalContext FrontendStages.Declarations.renamedFunctionDeclarations
    [] FrontendStages.Declarations.translatedFunctions [] FrontendStages.Declarations.globalContext
    ⟨FrontendStages.Declarations.compileFunctionDeclarations_eq,
      List.all_eq_true.mp baseline_renamed_functions_kind⟩
  rw [compiled.2.2.2]
  exact functions_map_compile _ _

#print axioms functions_map_compile
#print axioms baseline_renamed_functions_kind
#print axioms baseline_compiled_functions
end InitECandidate.Runtime
