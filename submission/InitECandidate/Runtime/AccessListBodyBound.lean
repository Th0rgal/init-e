import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AccessListBodySource
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def accessBodyCost (length : Nat) : Nat :=
  length * ((2 * length + 1) * 15 + 19) + length * 12 + 4 +
    (length * (accessStepCost length length + 1) + 2)

theorem access_budget_transfer (first tailCost wanted before after : Nat)
    (monotone : wanted ≤ tailCost) (budget : first + 1 + tailCost ≤ before)
    (cost : before - 1 ≤ after + first) : wanted ≤ after := by omega

theorem access_after_slices_budget (length count before after : Nat)
    (countBound : count ≤ length) (budget : accessBodyCost length ≤ before)
    (cost : before - 1 ≤ after + (length * ((2 * length + 1) * 15 + 19) + length * 12 + 3)) :
    count * (accessStepCost length length + 1) + 2 ≤ after := by
  have factor := Nat.mul_le_mul_right (accessStepCost length length + 1) countBound
  apply access_budget_transfer _ _ _ before after (Nat.add_le_add_right factor 2) _ cost
  simpa only [accessBodyCost,← Nat.add_assoc] using budget

/-- Polynomial source-clock bound for the complete original authorization decoder,
including outer slicing, records allocation and every inner record traversal. -/
theorem evaluate_access_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + length.toNat * 40 + (length.toNat * 48 + 46) * length.toNat + length.toNat * 32 + 7 ≤ frame.toNat)
    (budget : accessBodyCost length.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_access_list)
    state.clock ≤ evaluated.2.clock + accessBodyCost length.toNat ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1
    dsimp [accessBodyCost] at budget
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) with
  | mk result bodyPost =>
    rw [bodyRun] at bounded
    have composed := evaluate_decCall_checked_continuation_bounded state bodyPost (ofString "lst") (ofString "rlp_list_to_slices")
      (.comb [.one,.one]) (.comb [.one,.one]) arguments [.val (.word pointer),.val (.word length)]
      (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) accessAfterSlices callee result
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4)
      (length.toNat * (accessStepCost length.toNat length.toNat + 1) + 2) args lookup
      (by dsimp [accessBodyCost] at budget; omega) bodyRun bounded.2.1
      (by have cost := bounded.1; change state.clock - 1 ≤ bodyPost.clock + _ at cost; omega) bounded.2.2 (by
        intro value returned _
        have actual := bodyRun
        rw [returned] at actual
        obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
          rlpSlices_body_returned_runtime_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
            atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
            heap arrayBound (by omega) heapArena entryBudget inputBeforeFrame inputBeforeArray value actual
        subst value
        let resumed := setVarHOLFinite (ofString "lst") (.rStruct [.val (.word array),.val (.word count)]) {bodyPost with locals := state.locals}
        have listLocal : resumed.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
          simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        have resumedSlices : RlpSliceInputPrefix resumed array pointer length count.toNat := by
          intro slot inside
          obtain ⟨p,n,item⟩ := slices slot inside
          exact ⟨p,n,RlpSliceInputEntry.after_frame bodyPost resumed array slot p n pointer length item rfl rfl rfl⟩
        have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
        rw [actual] at metadata
        have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
          intro address lower upper
          change bodyPost.memaddrs address
          rw [metadata.2.1]
          exact arena address lower upper
        have product : (count * 16).toNat = count.toNat * 16 := by
          rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
          rfl
        have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
        have factor := Nat.mul_le_mul_right (accessStepCost length.toNat length.toNat + 1) countBound
        have tailBudget : count.toNat * (accessStepCost length.toNat length.toNat + 1) + 2 ≤ resumed.clock := by
          change count.toNat * (accessStepCost length.toNat length.toNat + 1) + 2 ≤ bodyPost.clock
          have cost := bounded.1
          change state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) at cost
          exact access_after_slices_budget length.toNat count.toNat state.clock bodyPost.clock countBound budget cost
        have nextNat : (allocationEnd array (count * 16)).toNat = array.toNat + count.toNat * 16 := by
          have sizeAligned : (count * 16).toNat % 8 = 0 := by rw [product]; omega
          rw [allocationEnd_aligned_toNat array (count * 16) (by rw [product]; exact interval) arrayAligned sizeAligned,product]
        have resumedHeapArena : ∀ address : BitVec 64, (allocationEnd array (count * 16)).toNat ≤ address.toNat →
            address.toNat < 33806089496 → resumed.memaddrs address := by
          intro address lower upper
          change bodyPost.memaddrs address
          rw [metadata.2.1]
          exact heapArena address (by rw [nextNat] at lower; omega) upper
        have growth := Nat.mul_le_mul_left (length.toNat * 48 + 46) countBound
        have tail := evaluate_access_allocation_bounded resumed array count (allocationEnd array (count * 16)) pointer length scratch frame ceiling inputLimit
          listLocal resumedSlices scratchPost framePost (metadata.1.trans code) resumedArena lengthBound limitBound orderedFrame framePositive
          scratchBelow (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
          (by rw [product] at covers; exact covers.1) aligned heapPost endpoint
          (by omega)
          resumedHeapArena (by omega) (by rw [nextNat]; omega) inputBeforeFrame (by rw [nextNat]; omega) tailBudget
        have large := Nat.add_le_add_right factor 2
        exact ⟨Nat.le_trans tail.1 (Nat.add_le_add_left large _),tail.2.1,tail.2.2.1⟩)
    have terminal := evaluate_access_body_terminal state
    rw [source_access_body]
    exact ⟨composed.1,composed.2.1,composed.2.2,by simpa only [source_access_body] using terminal⟩

#print axioms evaluate_access_body_bounded
end InitECandidate.Runtime
