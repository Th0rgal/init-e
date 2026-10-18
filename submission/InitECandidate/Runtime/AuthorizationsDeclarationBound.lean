import InitECandidate.Runtime.BlobHashesDeclarationBound
import InitECandidate.Runtime.AuthorizationsBodyBound
import InitECandidate.Runtime.OriginalAuthorizationsCode
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original authorization decoder with a straight continuation adds one
call tick to its checked polynomial body bound. -/
theorem evaluate_authorization_declaration_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : straightLine continuation = true)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + length.toNat * 248 ≤ frame.toNat)
    (budget : authorizationBodyCost length.toNat + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "decode_authorizations") arguments continuation)
    state.clock ≤ evaluated.2.clock + (authorizationBodyCost length.toNat + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_authorization_body_bounded entry pointer length scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayBeforeFrame arrayAligned reserve
    (by change authorizationBodyCost length.toNat ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_authorizations) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "decode_authorizations") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_decode_authorizations,.comb [.one,.one]) := by
      rw [code]; exact originalRuntimeCode_authorizations_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "decode_authorizations")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_decode_authorizations) (.comb [.one,.one]) pointer length (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    exact evaluate_decCall_straight_bounded state bodyPost name (ofString "decode_authorizations") (.comb [.one,.one]) (.comb [.one,.one]) arguments
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_decode_authorizations) continuation callee bodyResult
      (authorizationBodyCost length.toNat + 1) args lookup (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos _) budget)) bodyRun bound.2.1
      (by
        have cost := bound.1
        change state.clock - 1 ≤ bodyPost.clock + authorizationBodyCost length.toNat at cost
        exact blobHashes_call_clock_bound state.clock bodyPost.clock (authorizationBodyCost length.toNat)
          (Nat.lt_of_lt_of_le (Nat.succ_pos _) budget) cost) bound.2.2.1 supported

#print axioms evaluate_authorization_declaration_bounded
end InitECandidate.Runtime
