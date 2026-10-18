import InitECandidate.Runtime.AuthorizationsInnerSlicesBound
import InitECandidate.Runtime.AccessListEntryCheckBound
import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
import InitECandidate.Runtime.AuthorizationsEntryCheckBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BlobHashesDeclarationBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessInnerSlicesCost (length inputLength : Nat) : Nat :=
  length * ((2 * length + 1) * 15 + 19) + length * 12 + 4 +
    ((inputLength * ((2 * inputLength + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength)

theorem source_access_inner_slices : accessInnerSlices =
    .decCall (ofString "ent") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] accessEntryCheck := by
  simp only [accessInnerSlices,accessEntryCheck,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Inner entry slicing establishes the prefix and heap frontier for the remaining access-list record. -/
theorem evaluate_access_inner_slices_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
        some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (inputStarts : input.toNat ≤ pointer.toNat)
    (inputEnds : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (reserve : array.toNat + length.toNat * 16 + 7 + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : accessInnerSlicesCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessInnerSlices
    state.clock ≤ evaluated.2.clock + accessInnerSlicesCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3
  let tailCost := ((inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat)
  have total : first + 1 + tailCost ≤ state.clock := by
    simpa only [first,tailCost,accessInnerSlicesCost,← Nat.add_assoc] using budget
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : first ≤ entry.clock := by
    change first ≤ state.clock - 1
    exact authorization_inner_entry_budget first tailCost state.clock total
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have bodyCost : state.clock - 1 ≤ post.clock + first := bounded.1
    have positive : 0 < state.clock := by have nonzero := authorization_inner_entry_budget first tailCost state.clock total; omega
    rw [source_access_inner_slices]
    have composed := evaluate_decCall_checked_continuation_bounded state post (ofString "ent") (ofString "rlp_list_to_slices")
      (.comb [.one,.one]) (.comb [.one,.one])
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))]
      [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
      accessEntryCheck callee result (first + 1) tailCost args lookup (Nat.ne_of_gt positive) bodyRun bounded.2.1
      (blobHashes_call_clock_bound _ _ _ positive bodyCost) bounded.2.2 ?_
    · simpa only [first,tailCost,accessInnerSlicesCost,← Nat.add_assoc] using composed
    · intro value returned checked
      have actual := bodyRun
      rw [returned] at actual
      obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
        rlpSlices_body_returned_runtime_contract entry post pointer length scratch frame array ceiling inputLimit
          atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
          scratchBelow arena heap arrayBound (by omega) heapArena entryBudget inputBeforeFrame inputBeforeArray value actual
      subst value
      have outerSlices := slices.within_outer post array pointer length input inputLength count.toNat inputStarts inputEnds
      let resumed := setVarHOLFinite (ofString "ent") (.rStruct [.val (.word array),.val (.word count)]) {post with locals := state.locals}
      have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
        intro slot inside
        obtain ⟨p,n,item⟩ := outerSlices slot inside
        exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
      have atEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
      rw [actual] at metadata
      have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
        intro address lower upper
        change post.memaddrs address
        rw [metadata.2.1]
        exact arena address lower upper
      have tailBudget : tailCost ≤ resumed.clock := by
        change tailCost ≤ post.clock
        exact blobHashes_budget_transfer first tailCost tailCost state.clock post.clock (Nat.le_refl _) total bodyCost
      have product : (count * 16).toNat = count.toNat * 16 := by
        rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
        rfl
      have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
      rw [product] at covers
      have resumedHeapArena : ∀ address : BitVec 64, (allocationEnd array (count * 16)).toNat ≤ address.toNat →
          address.toNat < 33806089496 → resumed.memaddrs address := by
        intro address lower upper
        change post.memaddrs address
        rw [metadata.2.1]
        exact heapArena address (by omega) upper
      exact evaluate_access_entry_check_bounded resumed array count input inputLength scratch frame (allocationEnd array (count * 16))
        ceiling inputLimit atEntry resumedPrefix inputBound limitBound scratchPost framePost (metadata.1.trans code)
        orderedFrame framePositive scratchBelow resumedArena
        (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
        heapPost endpoint countLimit resumedHeapArena (by omega) (by omega) tailBudget

#print axioms evaluate_access_inner_slices_bounded
end InitECandidate.Runtime
