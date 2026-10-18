import InitECandidate.Runtime.BlobHashesBodyGuardedHeap
import InitECandidate.Runtime.BlobHashesBodyWholeInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem blobHashes_body_returned_whole_input_guarded_heap {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
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
    (budget : blobHashesBodyCost inputLength.toNat ≤ state.clock)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_blob_hashes) = (some (.returned finalValue),final)) :
    ∃ count heap : BitVec 64, count.toNat ≤ length.toNat ∧
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat = array.toNat + count.toNat * 48 ∧ heap.toNat ≤ 33806089496 ∧
      heap.toNat % 8 = 0 ∧ heap.toNat ≤ array.toNat + length.toNat * 48 := by
  have nested : length.toNat ≤ inputLength.toNat := by omega
  exact blobHashes_body_returned_guarded_heap state final pointer length input inputLength scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound inputBound starts ends limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove arrayAligned
    (Nat.le_trans (blobHashes_mixed_body_cost_le length.toNat inputLength.toNat nested) budget) finalValue run

#print axioms blobHashes_body_returned_whole_input_guarded_heap
end InitECandidate.Runtime
