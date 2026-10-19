import InitECandidate.Runtime.DecodeCompletedNodeLeaf
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_leaf_branch_completed_node {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (array slicePointer sliceLength scratch frame pointer length heap nibs count flag : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 slicePointer sliceLength)
    (noWrap : slicePointer.toNat + sliceLength.toNat < 2^64)
    (lengthBound : sliceLength.toNat ≤ inputLimit) (limitBound : inputLimit+9 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : sliceLength.toNat*((2*sliceLength.toNat+1)*15+19)+92633 ≤ s.clock)
    (value : ValueHOL 64) (node : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node)])
    (run : evaluateHOLFiniteState s decodeStepLeafBranch = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee slicePointer sliceLength)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word slicePointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word sliceLength)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) decodeStepLeafItemArguments =
      some [.val (.word slicePointer),.val (.word sliceLength)] := by
    simp [decodeStepLeafItemArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
      show s.memaddrs (array+16#64) from by simpa using slice.pointerDomain,
      show s.memory (array+16#64) = .word slicePointer from by simpa using slice.pointerCell,
      show s.memaddrs (array+24#64) from by simpa [BitVec.add_assoc] using slice.lengthDomain,
      show s.memory (array+24#64) = .word sliceLength from by simpa [BitVec.add_assoc] using slice.lengthCell]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) slicePointer sliceLength (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  rw [source_decode_step_leaf_branch] at run
  obtain ⟨parsed,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "vi") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_rlp_item) decodeStepLeafValueContinuation
      (rlpHeaderCallee slicePointer sliceLength) value args lookup run
  obtain ⟨kind,pp,payload,consumed,rfl,starts,ends,span,small,scratchPost,framePost,heapPost⟩ :=
    rlpItem_body_returned_runtime_contract entry bodyPost slicePointer sliceLength scratch frame ceiling inputLimit p n
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change _ ≤ s.clock-1; omega) parsed bodyRun
  let ready := setVarHOLFinite (ofString "vi")
    (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)])
    {bodyPost with locals := s.locals}
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  have hp : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := heapPost.trans atHeap
  have localP : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vi" ≠ ofString "p" by decide] using atPointer
  have localN : ready.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vi" ≠ ofString "n" by decide] using atLength
  have localCn : ready.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vi" ≠ ofString "cn" by decide] using atPath
  have localVi : ready.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have result := decode_step_leaf_value_completed_node ready output
    pointer length heap nibs count flag kind pp payload consumed localP localN localCn localVi hp heapBound
      (metadata.1.trans code) value node completed tailRun
  rw [postEq]
  exact result

#print axioms decode_step_leaf_branch_completed_node
end InitECandidate.Runtime
