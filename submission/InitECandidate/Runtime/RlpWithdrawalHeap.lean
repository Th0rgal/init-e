import InitECandidate.Runtime.RlpWithdrawalGlobals
import InitECandidate.Runtime.RlpWithdrawalWriter
import InitECandidate.Runtime.HtabGrowTop
import InitECandidate.Runtime.AllocationSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem wdAssign_globals_frame : OriginalGlobalsFrame wdAssign := by
  rw [wdAssign]
  exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem wdFinishTail_globals_frame : OriginalGlobalsFrame wdFinishTail := by
  rw [wdFinishTail]
  apply globalsFrame_declCall_step originalRuntimeCode_rlp_finish_list_lookup
    rlpFinishList_globals_frame
  exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem wdCall36_globals_frame : OriginalGlobalsFrame wdCall36 := by
  rw [wdCall36]
  exact globalsFrame_localCall_step originalRuntimeCode_rlp_encode_word_lookup
    rlpEncodeWord_globals_frame

theorem wdCall36Tail_globals_frame : OriginalGlobalsFrame wdCall36Tail := by
  rw [wdCall36Tail]
  exact originalGlobalsFrame_sequence _ _ wdAssign_globals_frame wdFinishTail_globals_frame

theorem wdCallBytes_globals_frame : OriginalGlobalsFrame wdCallBytes := by
  rw [wdCallBytes]
  exact globalsFrame_localCall_step originalRuntimeCode_rlp_encode_bytes_lookup
    rlpEncodeBytes_globals_frame

theorem wdCallBytesTail_globals_frame : OriginalGlobalsFrame wdCallBytesTail := by
  rw [wdCallBytesTail]
  exact originalGlobalsFrame_sequence _ _ wdAssign_globals_frame
    (originalGlobalsFrame_sequence _ _ wdCall36_globals_frame wdCall36Tail_globals_frame)

theorem wdCall8_globals_frame : OriginalGlobalsFrame wdCall8 := by
  rw [wdCall8]
  exact globalsFrame_localCall_step originalRuntimeCode_rlp_encode_word_lookup
    rlpEncodeWord_globals_frame

theorem wdCall8Tail_globals_frame : OriginalGlobalsFrame wdCall8Tail := by
  rw [wdCall8Tail]
  exact originalGlobalsFrame_sequence _ _ wdAssign_globals_frame
    (originalGlobalsFrame_sequence _ _ wdCallBytes_globals_frame wdCallBytesTail_globals_frame)

theorem wdCall0Tail_globals_frame : OriginalGlobalsFrame wdCall0Tail := by
  rw [wdCall0Tail]
  exact originalGlobalsFrame_sequence _ _ wdAssign_globals_frame
    (originalGlobalsFrame_sequence _ _ wdCall8_globals_frame wdCall8Tail_globals_frame)

theorem wdCall0_globals_frame : OriginalGlobalsFrame wdCall0 := by
  rw [wdCall0]
  apply globalsFrame_declCall_step originalRuntimeCode_rlp_encode_word_lookup
    rlpEncodeWord_globals_frame
  exact wdCall0Tail_globals_frame

theorem wdDecP_globals_frame : OriginalGlobalsFrame wdDecP := by
  rw [wdDecP]
  exact originalGlobalsFrame_declaration _ _ _ _ wdCall0_globals_frame

/-- A successful `encode_withdrawal_rlp` changes exactly one global: `heap_ptr` becomes the aligned
end of its own 64-byte buffer allocation.  The allocation writes that pointer and the writer tail
then keeps every global. -/
theorem rlpEncodeWithdrawal_returned_globals {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode) (clock : 2 ≤ t.clock)
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals =
      (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd B 64))) t).globals := by
  rw [source_rlpEncodeWithdrawal_body,rlpEncodeWithdrawal_eq] at run
  obtain ⟨values,body,callee,returnShape,w,bodyPost,resumed,inner,argsR,lookupR,bodyRun,_,_,_,rcode,rglob,
    _,_,_,rrun,_,_,_,_,pg⟩ := decCall_returned_globalsG run
  have argsEval : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [(.const (64#64))] = some [.val (.word (64#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  rw [argsEval] at argsR
  cases argsR
  have installed : t.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  rw [pan_single_word_lookup t.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) (64#64) installed] at lookupR
  cases lookupR
  obtain ⟨_,_,hw,_,_,_,bcode,bg⟩ := alloc_body_returned _ bodyPost B 64 (by exact code) (by exact heap)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) w bodyRun
  subst hw
  have resumedCode : resumed.code = originalRuntimeCode := by
    rw [rcode,bcode]
    exact code
  have frame := wdDecP_globals_frame resumed resumedCode
  rw [rrun] at frame
  rw [pg]
  rw [frame,rglob]
  exact bg

/-- A successful `encode_withdrawal_rlp` really advances the heap pointer. -/
theorem rlpEncodeWithdrawal_heap {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode) (clock : 2 ≤ t.clock)
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd B 64))) := by
  rw [rlpEncodeWithdrawal_returned_globals t base B value heap code clock run]
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- A successful `encode_withdrawal_rlp` keeps every other global, in particular the slice array
pointer. -/
theorem rlpEncodeWithdrawal_other_globals {F : Type} (t base : PanSemStateFiniteExact 64 F)
    (B : BitVec 64) (value : ValueHOL 64) (name : MlS)
    (heap : t.globals.lookup (ofString "heap_ptr") = some (.val (.word B)))
    (code : t.code = originalRuntimeCode) (clock : 2 ≤ t.clock) (apart : name ≠ ofString "heap_ptr")
    (run : evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) =
      (some (.returned value),base)) :
    base.globals.lookup name = t.globals.lookup name := by
  rw [rlpEncodeWithdrawal_returned_globals t base B value heap code clock run]
  simp only [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,apart]

#print axioms rlpEncodeWithdrawal_returned_globals
#print axioms rlpEncodeWithdrawal_heap
#print axioms rlpEncodeWithdrawal_other_globals
end InitECandidate.Runtime
