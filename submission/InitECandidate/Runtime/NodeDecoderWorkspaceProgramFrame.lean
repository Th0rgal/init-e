import InitECandidate.Runtime.NodeDecoderWorkspaceFrame
import InitECandidate.Runtime.DecodeStepLeafValueCheck
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every program passing the checked decoder-callee closure retains the watched
workspace global in every outcome. -/
theorem evaluate_node_decoder_workspace {F : Type} (s : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (name : MlS) (member : name ∈ nodeDecoderWorkspace)
    (supported : keepsG name nodeDecoderGood program = true) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s program).2.globals.lookup name = s.globals.lookup name := by
  apply evaluate_keepsG name nodeDecoderGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact node_decoder_workspace_installed installed good name member
  · exact supported
  · exact code

/-- Completing a leaf never consumes or resets parser scratch, including the
value-type guard and all constructor failure paths. -/
theorem decode_step_leaf_value_workspace_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (member : name ∈ nodeDecoderWorkspace) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s decodeStepLeafValueContinuation).2.globals.lookup name = s.globals.lookup name := by
  apply evaluate_node_decoder_workspace s _ name member _ code
  rw [source_decodeStep_leaf_value_continuation,source_decodeStep_leaf_construction,source_decodeStep_leaf_stores]
  simp [keepsG,nodeDecoderGood]

#print axioms evaluate_node_decoder_workspace
#print axioms decode_step_leaf_value_workspace_frame
end InitECandidate.Runtime
