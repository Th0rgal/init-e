import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalDecodeHeaderCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

/-- These workspace pointers are assigned only during initialization. -/
def parserWorkspaceGlobals : List MlS :=
  [ofString "keccak_st",ofString "keccak_pad",ofString "mpt_nib_scratch"]

/-- Reuse the established conservative driver exclusions and additionally
exclude the two workspace initializers. -/
def parserWorkspaceGood (function : MlS) : Bool :=
  evGood function && !([ofString "keccak_init",ofString "mpt_init"].contains function)

/-- Kernel computation checks every installed original body and all three
workspace names; good calls remain inside the checked set. -/
theorem parser_workspace_program_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(parserWorkspaceGood entry.1) || parserWorkspaceGlobals.all
      (fun name => keepsG name parserWorkspaceGood entry.2.2.1)) = true := by
  decide_cbv

theorem parser_workspace_installed {function : MlS} {parameters : List (MlS × ShapeHOL)} {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : parserWorkspaceGood function = true) (name : MlS) (member : name ∈ parserWorkspaceGlobals) :
    keepsG name parserWorkspaceGood body = true := by
  have checked := List.all_eq_true.mp parser_workspace_program_check _ (originalRuntimeCode_mem installed)
  have allNames : parserWorkspaceGlobals.all (fun name => keepsG name parserWorkspaceGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem parser_workspace_good_bodies (name : MlS) (member : name ∈ parserWorkspaceGlobals) :
    ∀ function, parserWorkspaceGood function = true → ∀ values body callee shape,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,shape) →
      keepsG name parserWorkspaceGood body = true := by
  intro function good values body callee shape lookup
  obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
  exact parser_workspace_installed installed good name member

/-- Checked programs keep the workspace pointers at every fuel and outcome. -/
theorem evaluate_keeps_parser_workspace {F : Type} (name : MlS) (member : name ∈ parserWorkspaceGlobals)
    (program : ProgHOL 64) (supported : keepsG name parserWorkspaceGood program = true)
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s program).2.globals.lookup name = s.globals.lookup name :=
  evaluate_keepsG name parserWorkspaceGood (parser_workspace_good_bodies name member) program supported s code

theorem header_decoder_keeps_parser_workspace {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (member : name ∈ parserWorkspaceGlobals) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_header)).2.globals.lookup name = s.globals.lookup name :=
  evaluate_keeps_parser_workspace name member _
    (parser_workspace_installed originalRuntimeCode_decodeHeader_lookup (by decide) name member) s code

#print axioms parser_workspace_program_check
#print axioms parser_workspace_installed
#print axioms parser_workspace_good_bodies
#print axioms evaluate_keeps_parser_workspace
#print axioms header_decoder_keeps_parser_workspace
end InitECandidate.Runtime
