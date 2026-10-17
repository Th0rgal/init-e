import InitECandidate.Runtime.ScratchAllocationBodyBound
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original allocator call has a two-tick budget across success and
both rejection paths; no allocator-space premise is needed. -/
theorem evaluate_scratch_alloc_decCall_straight_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (pointer size frame : BitVec 64)
    (name : MlS) (shape : ShapeHOL) (continuation : ProgHOL 64)
    (supported : straightLine continuation = true)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word size)])
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (ticks : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape (ofString "scratch_alloc") [argument] continuation)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have sizeLocal : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,cost,remaining,noTimeout,_,_⟩ := evaluate_scratch_alloc_body_bounded
    entry pointer size frame scratchGlobal sizeLocal frameGlobal code (by change 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_scratchAllocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
  have entryClock : entry.clock = state.clock - 1 := rfl
  exact evaluate_decCall_straight_bounded state bodyPost name (ofString "scratch_alloc") shape .one
    [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_scratch_alloc) continuation callee bodyResult 2
    args lookup (by omega) bodyRun remaining (by change entry.clock ≤ bodyPost.clock + 1 at cost; omega)
    noTimeout supported

#print axioms evaluate_scratch_alloc_decCall_straight_bounded
end InitECandidate.Runtime
