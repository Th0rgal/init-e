import InitECandidate.Runtime.RlpListCountDeclarationBound
import InitECandidate.Runtime.RlpListCountBodyResult
import InitECandidate.Runtime.RlpSlicesAllocationUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpSlices_body : sourceFunctionBody Guest.guestFn_rlp_list_to_slices =
    .decCall (ofString "count") .one (ofString "rlp_list_count")
      [.var .local (ofString "p"),.var .local (ofString "len")] rlpSlicesAllocation := by
  simp only [rlpSlicesAllocation,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Input-quadratic bound for the complete original slice-building body,
including count validation, allocation rejection and slice stores. -/
theorem evaluate_rlpSlices_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have pointerLocal : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have lengthLocal : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bound := evaluate_rlpListCount_body_bounded entry pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_count) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "rlp_list_count") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_count,.one) := by
      rw [code]; exact originalRuntimeCode_rlpListCount_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_count")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_list_count) .one pointer length (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_count)
    rw [bodyRun] at metadata
    dsimp only at metadata
    have tailBound : ∀ value, bodyResult = some (.returned value) →
        let resumed := setVarHOLFinite (ofString "count") value {bodyPost with locals := state.locals}
        let evaluated := evaluateHOLFiniteState resumed rlpSlicesAllocation
        resumed.clock ≤ evaluated.2.clock + (length.toNat * 12 + 2) ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
      intro value returned
      have returnedRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_count) =
          (some (.returned value),bodyPost) := by rw [bodyRun,returned]
      obtain ⟨count,rfl,countBound,_,_⟩ := rlpListCount_body_returned_contract entry bodyPost pointer length scratch frame ceiling inputLimit
        pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock - 1; omega) value returnedRun
      let resumed := setVarHOLFinite (ofString "count") (.val (.word count)) {bodyPost with locals := state.locals}
      have pLocal : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "count" ≠ ofString "p" by decide] using atPointer
      have cLocal : resumed.locals.lookup (ofString "count") = some (.val (.word count)) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have tail := evaluate_rlpSlices_allocation_uniform_bounded resumed pointer count pLocal cLocal (metadata.1.trans code)
        (by change count.toNat * 12 + 2 ≤ bodyPost.clock; omega)
      change resumed.clock ≤ (evaluateHOLFiniteState resumed rlpSlicesAllocation).2.clock + (length.toNat * 12 + 2) ∧ _
      exact ⟨by omega,tail.2⟩
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "p"),.var .local (ofString "len")] = some [.val (.word pointer),.val (.word length)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength]
    have composed := evaluate_decCall_continuation_bounded state bodyPost (ofString "count") (ofString "rlp_list_count") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_rlp_list_count) rlpSlicesAllocation callee bodyResult
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) (length.toNat * 12 + 2)
      args lookup (by omega) bodyRun bound.2.1 (by omega) bound.2.2.1 tailBound
    rw [source_rlpSlices_body]
    exact ⟨by dsimp only at composed ⊢; omega,composed.2⟩

#print axioms evaluate_rlpSlices_body_bounded
end InitECandidate.Runtime
