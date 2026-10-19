import InitECandidate.Runtime.NodeDecoderWorkspaceFrame
import InitECandidate.Runtime.DecodeStepPathPushProgress
import InitECandidate.Runtime.DecodeStepBranchUniformBound
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-- Scratch allocation may move scratch_ptr, but retains frame_mem_ptr. -/
def decoderFrameGood (name : MlS) : Bool :=
  [ofString "compact_to_nibbles",ofString "key_to_nibbles",ofString "node_new_leaf",
   ofString "node_new_branch",ofString "scratch_alloc",ofString "alloc",ofString "memzero",
   ofString "mpt_fail",ofString "trap_with"].contains name
 theorem decoder_frame_global_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(decoderFrameGood entry.1) || keepsG (ofString "frame_mem_ptr") decoderFrameGood entry.2.2.1)=true := by
  decide_cbv
 theorem decoder_frame_global_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
    (good : decoderFrameGood function=true) : keepsG (ofString "frame_mem_ptr") decoderFrameGood body=true := by
  have checked := List.all_eq_true.mp decoder_frame_global_check _ (originalRuntimeCode_mem installed)
  simpa [good] using checked
 theorem evaluate_decoder_frame_global {F : Type} (s : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    (supported : keepsG (ofString "frame_mem_ptr") decoderFrameGood program=true)
    (code : s.code=originalRuntimeCode) :
    (evaluateHOLFiniteState s program).2.globals.lookup (ofString "frame_mem_ptr")=s.globals.lookup (ofString "frame_mem_ptr") := by
  apply evaluate_keepsG (ofString "frame_mem_ptr") decoderFrameGood
  · intro function good values body callee shape lookup
    obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
    exact decoder_frame_global_installed installed good
  · exact supported
  · exact code
 theorem decode_step_extension_suffix_frame_check : keepsG (ofString "frame_mem_ptr") decoderFrameGood decodeStepExtensionSuffix=true := by
  decide_cbv
 theorem decode_step_branch_construction_frame_check : keepsG (ofString "frame_mem_ptr") decoderFrameGood decodeStepBranchConstruction=true := by
  decide_cbv
 theorem decode_step_path_push_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (nibs count leaf scratch frame record : BitVec 64)
    (atPath : s.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
    (code : s.code=originalRuntimeCode) (ordered : frame≤scratch) (ticks : 3≤s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation=
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) := by
  by_cases zero : leaf=0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    have frameKept := evaluate_decoder_frame_global s decodeStepExtensionSuffix decode_step_extension_suffix_frame_check code
    rw [run] at frameKept
    exact frameKept.trans frameGlobal
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    obtain ⟨value,shape⟩ := decode_step_leaf_branch_returned_flag s post _ run
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj shape)).1
    have impossible : (1 : BitVec 64)=0 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (1 : BitVec 64)≠0) impossible)
#print axioms decoder_frame_global_check
#print axioms decoder_frame_global_installed
#print axioms evaluate_decoder_frame_global
#print axioms decode_step_extension_suffix_frame_check
#print axioms decode_step_branch_construction_frame_check
#print axioms decode_step_path_push_returned_frame
end InitECandidate.Runtime
