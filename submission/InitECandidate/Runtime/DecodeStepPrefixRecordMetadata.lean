import InitECandidate.Runtime.DecodeStepRecordTailMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem decode_step_compact_call_push_returned_fields {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame record arr originalPointer originalLength : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word originalPointer)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word originalLength)))
    (small : length.toNat + 4 < 2^64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (budget : length.toNat / 4 + 10 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactCall =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderRecordFields post record arr originalPointer originalLength 1 := by
  let entry := callEntryStateHOLFinite s (compactNibbleCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "pi")),.rfield 2 (.var .local (ofString "pi"))] =
      some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atItem]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
    (.comb [.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_compactNibble_lookup)
  have bounded := runBounded_compact_nibble_body entry pointer length small p n code
    (by change length.toNat / 4 + 6 ≤ s.clock - 1; omega)
  rw [source_decodeStep_compact_call] at run
  obtain ⟨decoded,bodyPost,output,bodyRun,shapes,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "cn") (ofString "compact_to_nibbles")
      (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_compact_to_nibbles) decodeStepCompactContinuation
      (compactNibbleCallee pointer length) _ args lookup run
  obtain ⟨nibs,count,leaf,rfl⟩ := value_three_words_of_checked_shape decoded shapes.1
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
  have scratchKept := compact_nibble_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeDecoderWorkspace])
  have frameKept := compact_nibble_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeDecoderWorkspace])
  rw [bodyRun] at metadata scratchKept frameKept
  unfold RunBounded at bounded
  rw [bodyRun] at bounded
  have ticks : 3 ≤ bodyPost.clock := by
    have spent := bounded.1
    change s.clock - 1 ≤ bodyPost.clock + (length.toNat / 4 + 6) at spent
    omega
  let ready := setVarHOLFinite (ofString "cn")
    (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]) {bodyPost with locals := s.locals}
  have other : ∀ name, name ≠ ofString "cn" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have result := decode_step_path_push_returned_fields ready output scratch frame arr originalPointer originalLength
    nibs count leaf record ((other _ (by decide)).trans at_arr) ((other _ (by decide)).trans at_p)
    ((other _ (by decide)).trans at_n) (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) ordered (metadata.1.trans code) ticks tailRun
  rw [postEq]
  exact result

#print axioms decode_step_compact_call_push_returned_fields
theorem decode_step_two_case_push_returned_fields {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame record originalPointer originalLength : BitVec 64) (ceiling inputLimit : Nat)
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word originalPointer)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word originalLength)))
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 0 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : (length.toNat*((2*length.toNat+1)*15+19)+92633) + (length.toNat / 4 + 10) ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepTwoCase =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderRecordFields post record array originalPointer originalLength 1 := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) decodeStepFirstItemArguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [decodeStepFirstItemArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atArray,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,
      show s.memaddrs array from by simpa using slice.pointerDomain,
      show s.memory array = .word pointer from by simpa using slice.pointerCell,
      show s.memaddrs (array + 8#64) from by simpa using slice.lengthDomain,
      show s.memory (array + 8#64) = .word length from by simpa using slice.lengthCell]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit p n
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock - 1; omega)
  rw [source_decode_step_first_item] at run
  obtain ⟨decoded,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "pi") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_rlp_item) decodeStepFirstItemTail
      (rlpHeaderCallee pointer length) _ args lookup run
  obtain ⟨kind,pp,payload,consumed,rfl,_,_,span,payloadBound,scratchPost,framePost,_⟩ :=
    rlpItem_body_returned_runtime_contract entry bodyPost pointer length scratch frame ceiling inputLimit p n
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change _ ≤ s.clock - 1; omega) decoded bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  rw [bodyRun] at bounded
  have divided : payload.toNat / 4 ≤ length.toNat / 4 := Nat.div_le_div_right payloadBound
  have ticks : payload.toNat / 4 + 10 ≤ bodyPost.clock := by
    have spent := bounded.1
    change s.clock - 1 ≤ bodyPost.clock + (length.toNat*((2*length.toNat+1)*15+19)+92632) at spent
    omega
  let resumed := setVarHOLFinite (ofString "pi")
    (.rStruct [.val (.word kind),.val (.word pp),.val (.word payload),.val (.word consumed)])
    {bodyPost with locals := s.locals}
  change evaluateHOLFiniteState resumed decodeStepFirstItemTail = _ at tailRun
  rw [source_decode_step_first_item_guard] at tailRun
  obtain ⟨next,normal,compactRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl resumed v) tailRun
  have same := mpt_fail_guard_normal_state resumed next _ 5 (metadata.1.trans code) normal
  subst next
  have other : ∀ name, name ≠ ofString "pi" → resumed.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have result := decode_step_compact_call_push_returned_fields resumed output kind pp payload consumed scratch frame record
    array originalPointer originalLength ((other _ (by decide)).trans atArray) ((other _ (by decide)).trans at_p)
    ((other _ (by decide)).trans at_n) (by omega) (by simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    scratchPost framePost (metadata.1.trans code) orderedFrame ticks compactRun
  rw [postEq]
  exact result

#print axioms decode_step_two_case_push_returned_fields
end InitECandidate.Runtime
