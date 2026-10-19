import InitECandidate.Runtime.ResolveStepSource
import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalNodeNewHashedCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

def resolveStepGood (name : MlS) : Bool :=
  [ofString "node_new_hashed",ofString "alloc",ofString "trap_with",ofString "mpt_fail",
    ofString "nodedb_lookup",ofString "htab_get",ofString "htab_find_slot",ofString "htab_hash",ofString "memeq"].contains name

def resolveStepWorkspace : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr"]

/-- Actual constructor callees retain both parser workspace globals, including
allocation failures and memory errors. Heap allocation remains permitted. -/
theorem resolve_step_workspace_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(resolveStepGood entry.1) || resolveStepWorkspace.all
      (fun name => keepsG name resolveStepGood entry.2.2.1)) = true := by
  decide_cbv

theorem resolve_step_workspace_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : resolveStepGood function = true) (name : MlS) (member : name ∈ resolveStepWorkspace) :
    keepsG name resolveStepGood body = true := by
  have checked := List.all_eq_true.mp resolve_step_workspace_check _ (originalRuntimeCode_mem installed)
  have allNames : resolveStepWorkspace.all (fun name => keepsG name resolveStepGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem node_new_hashed_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ resolveStepWorkspace) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_hashed)).2.globals.lookup name =
      s.globals.lookup name := by
  apply evaluate_keepsG name resolveStepGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact resolve_step_workspace_installed installed good name member
  · exact resolve_step_workspace_installed originalRuntimeCode_nodeNewHashed_lookup (by decide) name member
  · exact code

/-- All non-parser resolver branches preserve the restored parser workspace. -/
theorem resolve_step_tail_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ resolveStepWorkspace) :
    (evaluateHOLFiniteState s (resolveStepAt 3)).2.globals.lookup name = s.globals.lookup name := by
  apply evaluate_keepsG name resolveStepGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact resolve_step_workspace_installed installed good name member
  · have names : name = ofString "scratch_ptr" ∨ name = ofString "frame_mem_ptr" := by
      simpa [resolveStepWorkspace] using member
    rcases names with rfl | rfl <;>
      simp only [source_resolve_step_kind,source_resolve_step_string,source_resolve_step_lookup,
        source_resolve_step_lookup_tail,source_resolve_step_hashed] <;> decide_cbv
  · exact code
#print axioms resolve_step_tail_workspace_frame

#print axioms resolve_step_workspace_check
#print axioms resolve_step_workspace_installed
#print axioms node_new_hashed_workspace_frame
end InitECandidate.Runtime
