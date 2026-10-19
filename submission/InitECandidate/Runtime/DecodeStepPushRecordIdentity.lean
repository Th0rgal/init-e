import InitECandidate.Runtime.DecodeStepEntryPushProgress
import InitECandidate.Runtime.DecodeStepFreshRecordPointer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem push_pair_record_eq (record expected : BitVec 64)
    (same : ValueHOL.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)] =
      .rStruct [.val (.word (1 : BitVec 64)),.val (.word expected)]) : record = expected := by
  exact HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj (ValueHOL.rStruct.inj same)).2).1)


theorem decode_step_extension_suffix_returned_pointer {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) (value : ValueHOL 64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (ticks : 3 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepExtensionSuffix = (some (.returned value),post)) :
    value = .rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd scratch 88))] := by
  rw [source_decodeStep_extension_suffix] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 7 code normal
  subst next
  exact decode_step_extension_record_returned_pointer s post scratch frame value scratchGlobal frameGlobal
    ordered code (by omega) tailRun


theorem decode_step_branch_construction_returned_pointer {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (scratch frame : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : 43 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch)
    (run : evaluateHOLFiniteState state decodeStepBranchConstruction = (some (.returned value),post)) :
    value = .rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd scratch 88))] := by
  let entry := callEntryStateHOLFinite state (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  have lookup := pan_no_args_lookup state.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch)
    (by rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup)
  rw [source_decode_step_branch_construction] at run
  obtain ⟨allocated,bodyPost,output,bodyRun,_,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope state post (ofString "br") (ofString "node_new_branch") .one .one [] []
      (sourceFunctionBody Guest.guestFn_node_new_branch) decodeStepBranchRecord HolFiniteMapExact.empty value rfl lookup run
  have bound := runBounded_node_new_branch_body entry code (by change 40 ≤ state.clock - 1; omega)
  unfold RunBounded at bound
  rw [bodyRun] at bound
  have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
  have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
  have metadata :=  evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
  rw [bodyRun] at scratchKept frameKept metadata
  have result := decode_step_branch_record_returned_pointer
    (setVarHOLFinite (ofString "br") allocated {bodyPost with locals := state.locals}) output scratch frame value
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) ordered (metadata.1.trans code)
    (by change 2 ≤ bodyPost.clock; have spent := bound.1; change state.clock - 1 ≤ bodyPost.clock + 40 at spent; omega)
    tailRun
  exact result



theorem decode_step_seventeen_returned_record {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array scratch frame : BitVec 64) (record : BitVec 64)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word (17#64))]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (budget : 43 ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) = (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  rw [evaluate_decode_step_seventeen s array atSlices] at run
  exact push_pair_record_eq record _ (decode_step_branch_construction_returned_pointer s post scratch frame _ code budget
    scratchGlobal frameGlobal ordered run)


theorem decode_step_path_push_returned_record {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (nibs count leaf scratch frame record : BitVec 64)
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (ticks : 3 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  by_cases zero : leaf = 0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    exact push_pair_record_eq record _ (decode_step_extension_suffix_returned_pointer s post scratch frame _
      scratchGlobal frameGlobal code ordered ticks run)
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    obtain ⟨value,shape⟩ := decode_step_leaf_branch_returned_flag s post _ run
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj shape)).1
    have impossible : (1 : BitVec 64) = 0 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (1 : BitVec 64) ≠ 0) impossible)


theorem decode_step_compact_call_push_returned_record {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame record : BitVec 64)
    (small : length.toNat + 4 < 2^64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (budget : length.toNat / 4 + 10 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactCall =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
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
  have result := decode_step_path_push_returned_record
    (setVarHOLFinite (ofString "cn") (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)])
      {bodyPost with locals := s.locals}) output nibs count leaf scratch frame record
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) (metadata.1.trans code) ordered ticks tailRun
  exact result


theorem decode_step_two_case_push_returned_record {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
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
    record = scratchAllocationEnd scratch 88 := by
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
  have result := decode_step_compact_call_push_returned_record resumed output kind pp payload consumed scratch frame record
    (by omega) (by simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    scratchPost framePost (metadata.1.trans code) orderedFrame ticks compactRun
  exact result


theorem decode_step_list_push_returned_record {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array count input inputLength scratch frame record : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepListPushCost inputLimit ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  by_cases two : count = 2
  · subst count
    obtain ⟨pointer,length,entry⟩ := table 0 (by decide)
    have lengthBound : length.toNat ≤ inputLimit :=
      (entry.length_bound s array 0 pointer length input inputLength).trans inputBound
    have product : length.toNat*((2*length.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
      Nat.mul_le_mul lengthBound (by omega)
    have divided : length.toNat / 4 ≤ inputLimit / 4 := Nat.div_le_div_right lengthBound
    rw [evaluate_decode_step_two_items s array atSlices] at run
    exact decode_step_two_case_push_returned_record s post array pointer length scratch frame record ceiling inputLimit
      atArray entry.readable entry.noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena (by unfold decodeStepListPushCost at budget; omega) run
  · by_cases seventeen : count = 17
    · subst count
      exact decode_step_seventeen_returned_record s post array scratch frame _ atSlices scratchGlobal frameGlobal
        code orderedFrame (by unfold decodeStepListPushCost at budget; omega) run
    · rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices] at run
      have noReturn := evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4]
        (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])
      exact False.elim (noReturn (congrArg Prod.fst run))

/-- The actual array declaration preserves the list table and introduces no
clock cost before the original list dispatch. -/

theorem decode_step_array_push_returned_record {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array count input inputLength scratch frame record : BitVec 64)
    (ceiling inputLimit : Nat)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepListPushCost inputLimit ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 5) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  rw [source_decode_step_array] at run
  obtain ⟨value,output,evaluated,bodyRun,postEq⟩ := evaluate_dec_returned_scope s post (ofString "arr") .one
    (.rfield 0 (.var .local (ofString "sl"))) (decodeStepAt 6) _ run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield 0 (.var .local (ofString "sl"))) = some (.val (.word array)) := by
    simp [evalHOLExact,atSlices]
  rw [evalArray] at evaluated
  cases evaluated
  let entered := setVarHOLFinite (ofString "arr") (.val (.word array)) s
  have enteredTable : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro index inside
    obtain ⟨p,n,entry⟩ := table index inside
    exact ⟨p,n,entry.after_frame _ _ _ _ _ _ _ _ rfl rfl rfl⟩
  have result := decode_step_list_push_returned_record entered output array count input inputLength scratch frame record
    ceiling inputLimit (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "sl" by decide] using atSlices)
    enteredTable inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  exact result


theorem decode_step_slices_push_returned_record {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepListPushCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 4) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  have reached := decode_step_slices_runtime_reaches s pointer length consumed scratch frame array ceiling inputLimit
    atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by omega) heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 4) (decodeStepAt 5)
    _ _ _ reached (by rw [run])
  obtain ⟨count,atSlices,_,table,_,scratchReady,frameReady,_,_,_,codeReady,domainReady⟩ := facts
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 5) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    have progress := decode_step_array_push_returned_record ready output array count pointer length scratch frame record
      ceiling inputLimit atSlices table lengthBound limitBound scratchReady frameReady (codeReady.trans code)
      orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      (by omega) tailRun
    exact progress


theorem decode_step_kind_push_returned_record {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (parsedKind : kind = 0 ∨ kind = 1)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepListPushCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 3) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  rcases parsedKind with zeroKind | listKind
  · subst kind
    by_cases zero : length = 0
    · subst length
      rw [evaluate_decode_step_empty_bytes s pointer consumed atItem] at run
      have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
      have words := (List.cons.inj (ValueHOL.rStruct.inj values)).1
      have impossible : (0#64) = (1 : BitVec 64) := HolWordLab.word.inj (ValueHOL.val.inj words)
      exact False.elim ((by decide : (0#64) ≠ (1 : BitVec 64)) impossible)
    · rw [evaluate_decode_step_nonempty_bytes s pointer length consumed zero code atItem] at run
      have noReturn := evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4]
        (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])
      exact False.elim (noReturn (congrArg Prod.fst run))
  · subst kind
    rw [evaluate_decode_step_list_dispatch s pointer length consumed atItem] at run
    exact decode_step_slices_push_returned_record s post pointer length consumed scratch frame array record ceiling inputLimit
      atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget heap
      arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run


theorem decode_step_entry_push_returned_record {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepParseCost length.toNat + (decodeStepSlicesCost inputLimit + decodeStepListPushCost inputLimit) ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 0) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    record = scratchAllocationEnd scratch 88 := by
  have reached := decode_step_entry_parse_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 0) (decodeStepAt 3)
    _ _ _ reached (by rw [run])
  obtain ⟨kind,pp,payload,atItem,parsedKind,payloadBound,_,ends,span,starts,globals,codeReady,domainReady,_⟩ := facts
  have limit : payload.toNat ≤ inputLimit := payloadBound.trans lengthBound
  have product : payload.toNat*((2*payload.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
    Nat.mul_le_mul limit (by omega)
  have slicesCost : decodeStepSlicesCost payload.toNat ≤ decodeStepSlicesCost inputLimit := by
    unfold decodeStepSlicesCost
    omega
  have beforeFrame : pp.toNat + payload.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pp.toNat) := by
    rcases inputBeforeFrame with before | ⟨aligned,after⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨aligned,by omega⟩
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 3) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    have progress := decode_step_kind_push_returned_record ready output kind pp payload length scratch frame array record
      ceiling inputLimit atItem parsedKind span limit limitBound
      ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (codeReady.trans code)
      orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      (by omega) ((globals _).trans heap) arrayBound countLimit
      (by intro address lower upper; rw [domainReady]; exact heapArena address lower upper)
      beforeFrame (by omega) tailRun
    exact progress


#print axioms push_pair_record_eq

#print axioms decode_step_extension_suffix_returned_pointer

#print axioms decode_step_branch_construction_returned_pointer

#print axioms decode_step_seventeen_returned_record

#print axioms decode_step_path_push_returned_record

#print axioms decode_step_compact_call_push_returned_record

#print axioms decode_step_two_case_push_returned_record

#print axioms decode_step_list_push_returned_record

#print axioms decode_step_array_push_returned_record

#print axioms decode_step_slices_push_returned_record

#print axioms decode_step_kind_push_returned_record

#print axioms decode_step_entry_push_returned_record

end InitECandidate.Runtime
