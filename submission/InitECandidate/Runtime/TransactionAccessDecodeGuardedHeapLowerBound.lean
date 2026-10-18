import InitECandidate.Runtime.TransactionAccessDecodeBound
import InitECandidate.Runtime.AccessListBodyGuardedHeapLowerBound
import InitECandidate.Runtime.AccessListBodyHeapRuntimeContract
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual access declaration and result stores preserve final heap/global guarantees. -/
theorem transaction_access_decode_normal_guarded_heap_lower_bound {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "al") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (budget : accessBodyCost length.toNat + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessDecode = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      array.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "al")),.rfield 1 (.var .local (ofString "al"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  have installed : state.code.lookup (ofString "decode_access_list") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_access_list,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_accessList_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_access_list") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_access_list) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_transaction_access_decode] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "acc") (ofString "decode_access_list") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_decode_access_list) transactionAccessFinish callee args lookup run
  have ticks : accessBodyCost length.toNat ≤ entry.clock := by
    change accessBodyCost length.toNat ≤ state.clock - 1
    exact Nat.le_sub_of_add_le budget
  obtain ⟨nextHeap,binding,growth⟩ := access_body_returned_guarded_heap_lower_bound entry bodyPost pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound
    countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove arrayAligned ticks value bodyRun
  obtain ⟨count,contractHeap,_,_,_,scratchPost,framePost,heapPost,heapLimit,endAligned,_,_⟩ := access_body_returned_heap_runtime_contract
    entry bodyPost pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove arrayAligned ticks value bodyRun
  have same : nextHeap = contractHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (binding.symm.trans heapPost)))
  subst contractHeap
  let resumed := setVarHOLFinite (ofString "acc") value {bodyPost with locals := state.locals}
  have tailGlobals : ∀ watched, output.globals.lookup watched = bodyPost.globals.lookup watched := by
    intro watched
    have retained := evaluate_avoidsGlobalAssignment watched transactionAccessFinish (by rfl) resumed
    change evaluateHOLFiniteState resumed transactionAccessFinish = (none,output) at tailRun
    rw [tailRun] at retained
    exact retained
  rw [restored]
  exact ⟨nextHeap,(tailGlobals _).trans binding,growth,heapLimit,endAligned,
    (tailGlobals _).trans scratchPost,(tailGlobals _).trans framePost⟩

#print axioms transaction_access_decode_normal_guarded_heap_lower_bound
end InitECandidate.Runtime
