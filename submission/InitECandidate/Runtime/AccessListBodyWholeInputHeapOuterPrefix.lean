import InitECandidate.Runtime.AccessListBodyHeapIndependentOuterPrefix
import InitECandidate.Runtime.AccessListBodyWholeInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Whole-input clock budgets suffice for preservation by a nested access payload. -/
theorem access_body_returned_whole_input_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (wholeBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (wholeBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
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
    (budget : accessBodyCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_access_list) = (some (.returned finalValue),final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  have nested : length.toNat ≤ inputLength.toNat := by omega
  exact access_body_returned_heap_independent_outer_prefix state final pointer length input inputLength scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound inputBound starts ends wholeBeforeFrame wholeBeforeArray limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
    arrayAbove arrayAligned
    (Nat.le_trans (access_mixed_body_cost_le length.toNat inputLength.toNat nested) budget)
    watchedArray watchedCount watchedInput watchedLength watchedValid watchedAbove watchedBeforeArray finalValue run

#print axioms access_body_returned_whole_input_heap_outer_prefix
end InitECandidate.Runtime
