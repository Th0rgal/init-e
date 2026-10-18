import InitECandidate.Runtime.TransactionAuthorizationDecodeBound
import InitECandidate.Runtime.AuthorizationsBodyHeap
import InitECandidate.Runtime.AuthorizationsBodyGlobals
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual blob declaration and result stores preserve final heap/global guarantees. -/
theorem transaction_authorization_decode_normal_heap_growth {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "aul") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + length.toNat * 248 ≤ frame.toNat)
    (budget : authorizationBodyCost length.toNat + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationDecode = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      array.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ array.toNat + length.toNat * 232 ∧
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
      [.rfield 0 (.var .local (ofString "aul")),.rfield 1 (.var .local (ofString "aul"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  have installed : state.code.lookup (ofString "decode_authorizations") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_authorizations,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_authorizations_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_authorizations") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_decode_authorizations) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_transaction_authorization_decode] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "au") (ofString "decode_authorizations") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_decode_authorizations) transactionAuthorizationFinish callee args lookup run
  have ticks : authorizationBodyCost length.toNat ≤ entry.clock := by
    change authorizationBodyCost length.toNat ≤ state.clock - 1
    exact Nat.le_sub_of_add_le budget
  obtain ⟨count,nextHeap,countBound,binding,exactGrowth,heapLimit,endAligned,growth⟩ := authorization_body_returned_heap entry bodyPost
    pointer length pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound lengthBound
    (Nat.le_refl _) (Nat.le_refl _) inputBeforeFrame inputBeforeArray limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound
    countLimit heapArena inputBeforeFrame inputBeforeArray arrayBeforeFrame arrayAligned (by omega)
    (by simpa only [authorizationBodyCost] using ticks) value bodyRun
  have globals := authorization_body_returned_globals entry bodyPost pointer length pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound lengthBound (Nat.le_refl _) (Nat.le_refl _) inputBeforeFrame inputBeforeArray limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayBeforeFrame arrayAligned (by omega)
    (by simpa only [authorizationBodyCost] using ticks) value bodyRun
  let resumed := setVarHOLFinite (ofString "au") value {bodyPost with locals := state.locals}
  have tailGlobals : ∀ watched, output.globals.lookup watched = bodyPost.globals.lookup watched := by
    intro watched
    have retained := evaluate_avoidsGlobalAssignment watched transactionAuthorizationFinish (by rfl) resumed
    change evaluateHOLFiniteState resumed transactionAuthorizationFinish = (none,output) at tailRun
    rw [tailRun] at retained
    exact retained
  rw [restored]
  exact ⟨nextHeap,(tailGlobals _).trans binding,by omega,growth,heapLimit,endAligned,(tailGlobals _).trans globals.1,(tailGlobals _).trans globals.2⟩

#print axioms transaction_authorization_decode_normal_heap_growth
end InitECandidate.Runtime
