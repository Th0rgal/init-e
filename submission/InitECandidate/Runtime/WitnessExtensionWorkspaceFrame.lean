import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalNodeNewExtCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

def witnessExtensionGood (name : MlS) : Bool :=
  [ofString "node_new_ext",ofString "alloc",ofString "trap_with",ofString "mpt_fail"].contains name

def witnessExtensionWorkspace : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr"]

/-- Actual constructor callees retain both parser workspace globals, including
allocation failures and memory errors. Heap allocation remains permitted. -/
theorem witness_extension_workspace_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(witnessExtensionGood entry.1) || witnessExtensionWorkspace.all
      (fun name => keepsG name witnessExtensionGood entry.2.2.1)) = true := by
  decide_cbv

theorem witness_extension_workspace_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : witnessExtensionGood function = true) (name : MlS) (member : name ∈ witnessExtensionWorkspace) :
    keepsG name witnessExtensionGood body = true := by
  have checked := List.all_eq_true.mp witness_extension_workspace_check _ (originalRuntimeCode_mem installed)
  have allNames : witnessExtensionWorkspace.all (fun name => keepsG name witnessExtensionGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem node_new_ext_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ witnessExtensionWorkspace) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_ext)).2.globals.lookup name =
      s.globals.lookup name := by
  apply evaluate_keepsG name witnessExtensionGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact witness_extension_workspace_installed installed good name member
  · exact witness_extension_workspace_installed originalRuntimeCode_nodeNewExt_lookup (by decide) name member
  · exact code

/-- The complete original extension-unwind branch retains both workspace globals
on successful, rejected and failed-store outcomes. -/
theorem witness_extension_branch_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ witnessExtensionWorkspace) :
    (evaluateHOLFiniteState s witnessUnwindExtension).2.globals.lookup name = s.globals.lookup name := by
  apply evaluate_keepsG name witnessExtensionGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact witness_extension_workspace_installed installed good name member
  · have scratch : name = ofString "scratch_ptr" ∨ name = ofString "frame_mem_ptr" := by
      simpa [witnessExtensionWorkspace] using member
    rcases scratch with rfl | rfl <;>
      simp only [source_witness_extension,source_witness_extension_kind_scope,
        source_witness_extension_constructor,source_witness_extension_stores] <;> decide_cbv
  · exact code

#print axioms witness_extension_branch_workspace_frame

#print axioms witness_extension_workspace_check
#print axioms witness_extension_workspace_installed
#print axioms node_new_ext_workspace_frame
end InitECandidate.Runtime
