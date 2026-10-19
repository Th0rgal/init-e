import InitECandidate.Runtime.WitnessBranchFinishParseProgress
import InitECandidate.Runtime.WitnessBranchFinishSuffixMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_branch_finish_parse_normal_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame heap : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr2") = some (.val (.word array)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (run : evaluateHOLFiniteState s (witnessBranchFinishAt 1) = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16]]),
       .load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16],.const 8])] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,wordOpHOL,wordOp,panOpHOL,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact]
    have factor : (16 : BitVec 64)*16#64 = 256#64 := by decide
    have pd : s.memaddrs (array+256#64) := by simpa only [factor] using slice.pointerDomain
    have pc : s.memory (array+256#64) = .word pointer := by simpa only [factor] using slice.pointerCell
    have ld : s.memaddrs (array+264#64) := by
      simpa only [factor,BitVec.add_assoc,show 256#64+8#64 = 264#64 from by decide] using slice.lengthDomain
    have lc : s.memory (array+264#64) = .word length := by
      simpa only [factor,BitVec.add_assoc,show 256#64+8#64 = 264#64 from by decide] using slice.lengthCell
    rw [if_pos pd,pc,if_pos ld,lc]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  rw [source_witness_branch_finish_parse] at run
  obtain ⟨parsed,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ := evaluate_decCall_checked_normal_exact_scope
    s post (ofString "bv") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
    _ _ (sourceFunctionBody Guest.guestFn_rlp_item) (witnessBranchFinishAt 2) (rlpHeaderCallee pointer length)
    args lookup run
  have bodyBudget : length.toNat*((2*length.toNat+1)*15+19)+92632 ≤ entry.clock := by
    change _ ≤ s.clock-1
    unfold witnessBranchFinishCost at budget
    omega
  obtain ⟨kind,pp,payload,consumed,rfl,_,_,_,_,scratchPost,framePost,heapPost⟩ := rlpItem_body_returned_runtime_contract entry bodyPost
    pointer length scratch frame ceiling inputLimit p n inputRange lengthBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena bodyBudget parsed bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  let ready := setVarHOLFinite (ofString "bv")
    (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)]) {bodyPost with locals := s.locals}
  have readyBr : ready.locals.lookup (ofString "br") = some (.val (.word heap)) := by
    simpa (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atBr
  have readyValue : ready.locals.lookup (ofString "bv") = some
      (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨tailGlobals,tailMemory⟩ := witness_branch_finish_suffix_normal_memory_frame ready output
    heap kind pp payload consumed readyBr readyValue heapBound (metadata.1.trans code) tailRun
  rw [postEq]
  refine ⟨?_,?_,?_,?_⟩
  · change output.globals.lookup _=_
    rw [tailGlobals]
    exact scratchPost
  · change output.globals.lookup _=_
    rw [tailGlobals]
    exact framePost
  · change output.globals.lookup _=_
    rw [tailGlobals]
    exact heapPost
  · intro watched above below
    have memory := rlpItem_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit p n inputRange
      lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget _ bodyRun watched above
    change output.memory watched=s.memory watched
    exact (tailMemory watched below).trans memory

#print axioms witness_branch_finish_parse_normal_memory_frame
end InitECandidate.Runtime
