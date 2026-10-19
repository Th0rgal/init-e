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

/-- The actual decode call and either original caller continuation preserve
old upper-arena memory and have a monotone, aligned, capped heap frontier. -/
theorem witness_decode_mode_normal_heap_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      array.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
      ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < array.toNat →
        post.memory watched=s.memory watched := by
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
  have bodyHeap := decode_step_body_returned_heap_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change decodeStepBodyCost inputLimit ≤ s.clock-1; omega) heap arrayBound aligned countLimit heapArena
    inputBeforeFrame inputBeforeArray arrayAbove limitCap _ bodyRun
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,bodyMemory⟩ := bodyHeap
  let ready := setVarHOLFinite (ofString "d") (.rStruct [.val (.word flag),.val (.word node)])
    {bodyPost with locals := s.locals}
  have atD : ready.locals.lookup (ofString "d") = some (.rStruct [.val (.word flag),.val (.word node)]) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have topReady : ready.locals.lookup (ofString "top") = some (.val (.word previous)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "d" ≠ ofString "top" by decide] using atTop
  have heapFinal : post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) := by
    rw [postEq]
    change output.globals.lookup _ = _
    rw [globals]
    exact heapPost
  refine ⟨nextHeap,heapFinal,growth,capped,finishAligned,?_⟩
  rcases progress.1 with completed | pending
  · subst flag
    have exactTail := witness_decode_completed_normal_exact ready output node atD tailRun
    intro watched above before
    rw [postEq]
    change output.memory watched=s.memory watched
    rw [exactTail]
    exact bodyMemory watched above before
  · subst flag
    obtain ⟨_,_,_,recordBefore,_⟩ := decode_step_body_pushed_record_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
      (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change decodeStepBodyCost inputLimit ≤ s.clock-1; omega) heap arrayBound aligned countLimit heapArena
      inputBeforeFrame inputBeforeArray arrayAbove limitCap node bodyRun
    have linked := witness_decode_push_normal_link ready output node previous atD topReady tailRun
    intro watched above before
    rw [postEq]
    change output.memory watched=s.memory watched
    apply (linked.2 watched ?_).trans (bodyMemory watched above before)
    intro same
    have sameNat := congrArg BitVec.toNat same
    omega

#print axioms witness_decode_mode_normal_heap_frame
end InitECandidate.Runtime
