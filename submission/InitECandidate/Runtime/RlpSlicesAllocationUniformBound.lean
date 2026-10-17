import InitECandidate.Runtime.RlpSlicesAllocationBound
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original slice allocation and loop suffix has a count-linear bound
without any heap-global premise, including malformed heap state and rejection. -/
theorem evaluate_rlpSlices_allocation_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpSlicesAllocation
    state.clock ≤ evaluated.2.clock + (count.toNat * 12 + 2) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word (count * 16)))
  let entry := callEntryStateHOLFinite state callee
  have bound := evaluate_source_alloc_uniform_bounded entry code (by change 1 ≤ state.clock - 1; omega)
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_alloc) with
  | mk result post =>
    rw [run] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "alloc") =
        some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
      rw [code]; exact originalRuntimeCode_allocation_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
      (sourceFunctionBody Guest.guestFn_alloc) (count * 16) installed
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_alloc)
    rw [run] at metadata
    dsimp only at metadata
    have entryClock : entry.clock = state.clock - 1 := rfl
    have continuationBound : ∀ value, result = some (.returned value) →
        let resumed := setVarHOLFinite (ofString "arr") value {post with locals := state.locals}
        let evaluated := evaluateHOLFiniteState resumed rlpSlicesInitialized
        resumed.clock ≤ evaluated.2.clock + count.toNat * 12 ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
      intro value _
      let resumed := setVarHOLFinite (ofString "arr") value {post with locals := state.locals}
      have atPointer : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "arr" ≠ ofString "p" by decide] using pointerLocal
      have atCount : resumed.locals.lookup (ofString "count") = some (.val (.word count)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "arr" ≠ ofString "count" by decide] using countLocal
      have tail := evaluate_rlpSlices_initialized_bounded resumed pointer count atPointer atCount (metadata.1.trans code)
        (by change count.toNat * 12 ≤ post.clock; omega)
      exact ⟨tail.1,tail.2.1,tail.2.2.1⟩
    have composed := evaluate_decCall_continuation_bounded state post (ofString "arr") (ofString "alloc") .one .one
      [argument] [.val (.word (count * 16))] (sourceFunctionBody Guest.guestFn_alloc) rlpSlicesInitialized callee result 2 (count.toNat * 12)
      args lookup (by omega) run bound.2.1 (by omega) bound.2.2.1 continuationBound
    rw [source_rlpSlices_allocation]
    dsimp only [argument] at composed ⊢
    exact ⟨by omega,composed.2⟩

#print axioms evaluate_rlpSlices_allocation_uniform_bounded
end InitECandidate.Runtime
