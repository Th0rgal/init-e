import InitECandidate.Runtime.RlpSlicesBodyMemoryBefore
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.RlpListCountBodyBelow
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.RlpListCountBodyNamedGlobal
import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.RlpSlicesAllocationMemoryBefore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An earlier outer slice prefix survives successful public inner slicing,
including validation, heap allocation and all new slice stores. -/
theorem rlpSlices_body_returned_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post))
    (outerArray outerCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state outerArray input inputLength outerCount.toNat)
    (beforeArray : outerArray.toNat + outerCount.toNat * 16 ≤ array.toNat)
    (beforeFrame : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat) :
    RlpSliceInputPrefix post outerArray input inputLength outerCount.toNat := by
  obtain ⟨count,shape,countBound,filled,memoryFrame⟩ := rlpSlices_body_returned_memory_before state post
    pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena budget value run
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [run] at metadata
  by_cases order : array.toNat ≤ frame.toNat
  · apply RlpSliceInputPrefix.after_memory_below state post outerArray outerCount input inputLength array valid beforeArray metadata.2.1
    intro watched before
    exact memoryFrame watched before (Nat.lt_of_lt_of_le before order)
  · apply RlpSliceInputPrefix.after_memory_below state post outerArray outerCount input inputLength frame valid beforeFrame metadata.2.1
    intro watched before
    exact memoryFrame watched (by omega) before

#print axioms rlpSlices_body_returned_outer_prefix
end InitECandidate.Runtime
