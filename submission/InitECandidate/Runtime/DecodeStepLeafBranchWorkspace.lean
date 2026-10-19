import InitECandidate.Runtime.DecodeStepLeafBranchUniformBound
import InitECandidate.Runtime.NodeDecoderWorkspaceProgramFrame
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returning through the actual leaf-value parser and constructor restores the
original workspace frontier. Rejection and inaccessible byte paths cannot hide a
successful scratch release or allocation. -/
theorem decode_step_leaf_branch_returned_workspace {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat*((2*length.toNat+1)*15+19)+92637 ≤ s.clock) :
    ∀ value : ValueHOL 64, evaluateHOLFiniteState s decodeStepLeafBranch = (some (.returned value),post) →
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  intro value run
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) decodeStepLeafItemArguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [decodeStepLeafItemArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
      show s.memaddrs (array + 16#64) from by simpa using slice.pointerDomain,
      show s.memory (array + 16#64) = .word pointer from by simpa using slice.pointerCell,
      show s.memaddrs (array + 24#64) from by simpa [BitVec.add_assoc] using slice.lengthDomain,
      show s.memory (array + 24#64) = .word length from by simpa [BitVec.add_assoc] using slice.lengthCell]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  rw [source_decode_step_leaf_branch] at run
  obtain ⟨decoded,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "vi") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_rlp_item) decodeStepLeafValueContinuation
      (rlpHeaderCallee pointer length) value args lookup run
  obtain ⟨kind,pp,payload,consumed,rfl,_,_,_,_,scratchPost,framePost,_⟩ :=
    rlpItem_body_returned_runtime_contract entry bodyPost pointer length scratch frame ceiling inputLimit p n
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change _ ≤ s.clock - 1; omega) decoded bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  have keptScratch := decode_step_leaf_value_workspace_frame
    (setVarHOLFinite (ofString "vi")
      (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)])
      {bodyPost with locals := s.locals}) (ofString "scratch_ptr") (by simp [nodeDecoderWorkspace]) (metadata.1.trans code)
  have keptFrame := decode_step_leaf_value_workspace_frame
    (setVarHOLFinite (ofString "vi")
      (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)])
      {bodyPost with locals := s.locals}) (ofString "frame_mem_ptr") (by simp [nodeDecoderWorkspace]) (metadata.1.trans code)
  rw [tailRun] at keptScratch keptFrame
  rw [postEq]
  exact ⟨keptScratch.trans scratchPost,keptFrame.trans framePost⟩

#print axioms decode_step_leaf_branch_returned_workspace
end InitECandidate.Runtime
