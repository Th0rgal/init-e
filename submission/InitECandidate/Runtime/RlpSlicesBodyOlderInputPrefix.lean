import InitECandidate.Runtime.RlpSlicesBodyMemoryBefore
import InitECandidate.Runtime.TransactionMemzeroLowerFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_body_returned_older_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (older olderCount input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state older input inputLength olderCount.toNat)
    (before : older.toNat + olderCount.toNat * 16 ≤ array.toNat)
    (arrayBeforeFrame : array.toNat ≤ frame.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post)) :
    ∃ count : BitVec 64, value = .rStruct [.val (.word array),.val (.word count)] ∧ count.toNat ≤ length.toNat ∧
      RlpSlicePrefix post array count.toNat ∧ RlpSliceInputPrefix post older input inputLength olderCount.toNat := by
  obtain ⟨count,shape,bounded,readable,memory⟩ := rlpSlices_body_returned_memory_before state post pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound countLimit heapArena budget value run
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [run] at metadata
  refine ⟨count,shape,bounded,readable,?_⟩
  exact rlp_slice_input_prefix_after_lower_frame state post older olderCount input inputLength array valid before metadata.2.1
    (fun watched below => memory watched below (Nat.lt_of_lt_of_le below arrayBeforeFrame))

#print axioms rlpSlices_body_returned_older_input_prefix
end InitECandidate.Runtime
