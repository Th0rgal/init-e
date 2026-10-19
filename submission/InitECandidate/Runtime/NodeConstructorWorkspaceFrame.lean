import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalNodeNewBranchCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

def nodeConstructorGood (name : MlS) : Bool :=
  [ofString "node_new_branch",ofString "alloc",ofString "memzero",ofString "trap_with"].contains name

def nodeConstructorWorkspace : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr"]

/-- Actual constructor callees retain both parser workspace globals, including
allocation failures and memory errors. Heap allocation remains permitted. -/
theorem node_constructor_workspace_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(nodeConstructorGood entry.1) || nodeConstructorWorkspace.all
      (fun name => keepsG name nodeConstructorGood entry.2.2.1)) = true := by
  decide_cbv

theorem node_constructor_workspace_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : nodeConstructorGood function = true) (name : MlS) (member : name ∈ nodeConstructorWorkspace) :
    keepsG name nodeConstructorGood body = true := by
  have checked := List.all_eq_true.mp node_constructor_workspace_check _ (originalRuntimeCode_mem installed)
  have allNames : nodeConstructorWorkspace.all (fun name => keepsG name nodeConstructorGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem node_new_branch_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ nodeConstructorWorkspace) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_branch)).2.globals.lookup name =
      s.globals.lookup name := by
  apply evaluate_keepsG name nodeConstructorGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact node_constructor_workspace_installed installed good name member
  · exact node_constructor_workspace_installed originalRuntimeCode_nodeNewBranch_lookup (by decide) name member
  · exact code

#print axioms node_constructor_workspace_check
#print axioms node_constructor_workspace_installed
#print axioms node_new_branch_workspace_frame
end InitECandidate.Runtime
