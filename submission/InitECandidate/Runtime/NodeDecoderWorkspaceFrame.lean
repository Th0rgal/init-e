import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalCompactNibbleCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

def nodeDecoderGood (name : MlS) : Bool :=
  [ofString "compact_to_nibbles",ofString "key_to_nibbles",ofString "node_new_leaf",
    ofString "node_new_branch",ofString "alloc",ofString "memzero",ofString "mpt_fail",ofString "trap_with"].contains name

def nodeDecoderWorkspace : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr"]

/-- Actual compact-decoder and constructor callees retain both parser workspace globals, including
allocation failures and memory errors. Heap allocation remains permitted. -/
theorem node_decoder_workspace_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(nodeDecoderGood entry.1) || nodeDecoderWorkspace.all
      (fun name => keepsG name nodeDecoderGood entry.2.2.1)) = true := by
  decide_cbv

theorem node_decoder_workspace_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : nodeDecoderGood function = true) (name : MlS) (member : name ∈ nodeDecoderWorkspace) :
    keepsG name nodeDecoderGood body = true := by
  have checked := List.all_eq_true.mp node_decoder_workspace_check _ (originalRuntimeCode_mem installed)
  have allNames : nodeDecoderWorkspace.all (fun name => keepsG name nodeDecoderGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem compact_nibble_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (name : MlS) (member : name ∈ nodeDecoderWorkspace) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_compact_to_nibbles)).2.globals.lookup name =
      s.globals.lookup name := by
  apply evaluate_keepsG name nodeDecoderGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact node_decoder_workspace_installed installed good name member
  · exact node_decoder_workspace_installed originalRuntimeCode_compactNibble_lookup (by decide) name member
  · exact code

#print axioms node_decoder_workspace_check
#print axioms node_decoder_workspace_installed
#print axioms compact_nibble_workspace_frame
end InitECandidate.Runtime
