import InitECandidate.Runtime.DecodeStepEntryPushFrame
import InitECandidate.Runtime.DecodeStepReturnedProgress
import InitECandidate.Runtime.WitnessDecodeModeCapacity
import InitECandidate.Runtime.WitnessDecodeCompletedProgress
import InitECandidate.Runtime.WitnessDecodePushProgress
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual whole decode mode either delivers with unchanged stack capacity
and top, or consumes capacity, installs the fresh record and enters resolution. -/
theorem witness_decode_mode_normal_workspace_shape {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode = (none,post)) :
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    ((post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
      decoderScratchCapacity frame post = decoderScratchCapacity frame s ∧
      post.locals.lookup (ofString "top") = s.locals.lookup (ofString "top") ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (0#64)))) ∨
    (∃ record : BitVec 64, record = scratchAllocationEnd scratch 88 ∧
      post.globals.lookup (ofString "scratch_ptr")=some (.val (.word record)) ∧
      frame.toNat≤record.toNat ∧ record.toNat+88≤scratch.toNat ∧
      decoderScratchCapacity frame post < decoderScratchCapacity frame s ∧
      post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      ∃ slot : BitVec 64, (slot = 0 ∨ slot = 1) ∧
        post.locals.lookup (ofString "slot") = some (.val (.word slot)))) := by
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
  have capacity : decoderScratchCapacity frame post = decoderScratchCapacity frame bodyPost := by
    rw [postEq]
    unfold decoderScratchCapacity
    rw [globals]
    rfl
  have otherLocal (name : MlS) (different : name ≠ ofString "d") :
      post.locals.lookup name = output.locals.lookup name := by
    rw [postEq]
    exact restore_other_local _ _ name _ different
  have pointerLocal : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have lengthLocal : entry.locals.lookup (ofString "n")=some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyBudget : decodeStepBodyCost inputLimit≤entry.clock := by
    change decodeStepBodyCost inputLimit≤s.clock-1
    omega
  have finalGlobal (name : MlS) : post.globals.lookup name=bodyPost.globals.lookup name := by
    rw [postEq,globals]
    rfl
  rcases progress.1 with completed | pending
  · subst flag
    have kept := decode_step_body_completed_workspace entry bodyPost pointer length scratch frame array ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena bodyBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap
      (.val (.word node)) bodyRun
    have exactTail := witness_decode_completed_normal_exact
      (setVarHOLFinite (ofString "d") (.rStruct [.val (.word (0#64)),.val (.word node)]) {bodyPost with locals := s.locals})
      output node (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) tailRun
    refine ⟨(finalGlobal _).trans kept.2,Or.inl ⟨(finalGlobal _).trans kept.1,capacity.trans (progress.2.2.1 rfl),?_,?_⟩⟩
    · rw [otherLocal _ (by decide),exactTail]
      simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [otherLocal _ (by decide),exactTail]
      simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · subst flag
    have parseMono := decodeStepParseCost_mono length.toNat inputLimit lengthBound
    have listCost : decodeStepListPushCost inputLimit≤decodeStepTwoCaseCost inputLimit := by
      unfold decodeStepListPushCost decodeStepTwoCaseCost
      omega
    have pushBudget : decodeStepParseCost length.toNat+(decodeStepSlicesCost inputLimit+decodeStepListPushCost inputLimit)≤entry.clock :=
      (Nat.add_le_add parseMono (Nat.add_le_add_left listCost _)).trans bodyBudget
    have pushed := decode_step_entry_push_returned_progress entry bodyPost pointer length scratch frame array node ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray bodyRun
    have framePost := decode_step_entry_push_returned_frame entry bodyPost pointer length scratch frame array node ceiling inputLimit
      pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray bodyRun
    have control := witness_decode_push_normal_control
      (setVarHOLFinite (ofString "d") (.rStruct [.val (.word (1#64)),.val (.word node)]) {bodyPost with locals := s.locals})
      output node (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) tailRun
    obtain ⟨atTop,atMode,slot,slotBit,atSlot⟩ := control
    have identity := (progress.2.2.2 rfl).2
    refine ⟨(finalGlobal _).trans framePost,Or.inr ⟨node,identity,?_,?_,?_,?_,?_,?_,slot,slotBit,?_⟩⟩
    · rw [identity]
      exact (finalGlobal _).trans pushed.1
    · rw [identity];exact pushed.2.1
    · rw [identity];exact pushed.2.2
    · rw [capacity]
      exact (progress.2.2.2 rfl).1
    · rw [otherLocal _ (by decide)];exact atTop
    · rw [otherLocal _ (by decide)];exact atMode
    · rw [otherLocal _ (by decide)];exact atSlot

#print axioms witness_decode_mode_normal_workspace_shape
end InitECandidate.Runtime
