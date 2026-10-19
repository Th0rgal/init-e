import InitECandidate.Runtime.DecoderPushedTableLinkFrame
import InitECandidate.Runtime.WitnessDecodeModeCapacity
import InitECandidate.Runtime.WitnessDecodePushLink
import InitECandidate.Runtime.DecodeStepReturnedHeap
import InitECandidate.Runtime.DecodeStepPushedRecordContract
import InitECandidate.Runtime.WitnessDecodeCompletedProgress
import InitECandidate.Runtime.WitnessDecodePushProgress
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal original decode mode either completes or installs its actual fresh
record with real slice metadata and the actual WD_PREV link to the caller top. -/
theorem witness_decode_mode_normal_pushed_metadata {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array previous : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atPointer : s.locals.lookup (ofString "cur_p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "cur_n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit + 1 ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode = (none,post)) :
    (post.locals.lookup (ofString "mode") = some (.val (.word (0#64))) ∧
      post.locals.lookup (ofString "top") = s.locals.lookup (ofString "top")) ∨
    ∃ record : BitVec 64,
      post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      record = scratchAllocationEnd scratch 88 ∧ frame.toNat ≤ record.toNat ∧ record.toNat+88 ≤ scratch.toNat ∧
      (∀ offset : Nat, offset < 88 → post.memaddrs (record+BitVec.ofNat 64 offset)) ∧
      DecoderPushedTable post record pointer length pointer length ceiling ∧
      post.memory record = .word previous := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "db",.val (.word table))).update
    (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "cur_p"),.var .local (ofString "cur_n")] =
      some [.val (.word table),.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atPointer,atLength]
  have lookup := pan_three_word_shape_lookup s.code.lookup (ofString "_decode_step")
    (ofString "db") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn__decode_step)
    (.comb [.one,.one]) table pointer length (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeStep_lookup)
  rw [source_witness_decode_call] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_normal_exact_scope s post (ofString "d") (ofString "_decode_step")
      (.comb [.one,.one]) (.comb [.one,.one]) _ _ (sourceFunctionBody Guest.guestFn__decode_step)
      witnessDecodeTail callee args lookup run
  obtain ⟨flag,node,rfl⟩ := value_two_words_of_checked_shape value checked.1
  have progress := decode_step_body_returned_progress entry bodyPost pointer length scratch frame array ceiling inputLimit
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change decodeStepBodyCost inputLimit ≤ s.clock-1; omega)
    heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap flag node bodyRun
  have tailFrame : OriginalGlobalsFrame witnessDecodeTail := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_witness_decode_tail,source_witness_decode_completed,source_witness_decode_push]
    rfl
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__decode_step)
  rw [bodyRun] at metadata
  have globals := tailFrame
    (setVarHOLFinite (ofString "d") (.rStruct [.val (.word flag),.val (.word node)]) {bodyPost with locals := s.locals})
    (metadata.1.trans code)
  rw [tailRun] at globals
  let ready := setVarHOLFinite (ofString "d") (.rStruct [.val (.word flag),.val (.word node)])
    {bodyPost with locals := s.locals}
  have atD : ready.locals.lookup (ofString "d") = some (.rStruct [.val (.word flag),.val (.word node)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have topReady : ready.locals.lookup (ofString "top") = some (.val (.word previous)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "d" ≠ ofString "top" by decide] using atTop
  have otherLocal (name : MlS) (different : name ≠ ofString "d") :
      post.locals.lookup name = output.locals.lookup name := by
    rw [postEq]
    exact restore_other_local _ _ name _ different
  rcases progress.1 with completed | pending
  · subst flag
    have exactTail := witness_decode_completed_normal_exact ready output node atD tailRun
    refine Or.inl ⟨?_,?_⟩
    · rw [otherLocal _ (by decide),exactTail]
      simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [otherLocal _ (by decide),exactTail]
      simp (config := {decide := true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · subst flag
    obtain ⟨tableBody,identity,recordAfter,recordBefore,accessible⟩ := decode_step_body_pushed_record_contract
      entry bodyPost pointer length scratch frame array ceiling inputLimit
      (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change decodeStepBodyCost inputLimit ≤ s.clock-1; omega) heap arrayBound aligned countLimit heapArena
      inputBeforeFrame inputBeforeArray arrayAbove limitCap node bodyRun
    have linked := witness_decode_push_normal_link ready output node previous atD topReady tailRun
    have tailMetadata := evaluateHOLFiniteState_metadata ready witnessDecodeTail
    rw [tailRun] at tailMetadata
    have tableReady := tableBody.after_frame bodyPost ready node pointer length pointer length ceiling rfl rfl rfl
    have tableOutput := tableReady.after_link ready output node pointer length pointer length ceiling
      (by omega) globals tailMetadata.2.1 linked.2
    have tablePost : DecoderPushedTable post node pointer length pointer length ceiling := by
      rw [postEq]
      exact tableOutput.after_frame output _ node pointer length pointer length ceiling rfl rfl rfl
    obtain ⟨top,mode,slot,slotBit,atSlot⟩ := witness_decode_push_normal_control ready output node atD tailRun
    refine Or.inr ⟨node,?_,?_,identity,recordAfter,recordBefore,?_,tablePost,?_⟩
    · rw [otherLocal _ (by decide)]; exact top
    · rw [otherLocal _ (by decide)]; exact mode
    · intro offset inside
      rw [postEq]
      change output.memaddrs _
      rw [tailMetadata.2.1]
      exact accessible offset inside
    · rw [postEq]
      exact linked.1

#print axioms witness_decode_mode_normal_pushed_metadata
end InitECandidate.Runtime
