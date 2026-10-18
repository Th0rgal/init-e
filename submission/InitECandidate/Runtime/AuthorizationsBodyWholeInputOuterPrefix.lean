import InitECandidate.Runtime.AuthorizationsBodyIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsBodyWholeInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Whole-input budgets and reserves suffice for preservation by a nested authorization payload. -/
theorem authorization_body_returned_whole_input_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : authorizationBodyCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_authorizations) = (some (.returned finalValue),final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  have nested : length.toNat ≤ inputLength.toNat := by omega
  exact authorization_body_returned_independent_outer_prefix state final pointer length input inputLength scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound inputBound starts ends wholeBeforeFrame wholeBeforeArray limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
    (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 nested) _) arrayBeforeFrame) arrayAligned
    (authorization_mixed_reserve_le array.toNat length.toNat inputLength.toNat frame.toNat nested reserve)
    (Nat.le_trans (authorization_mixed_body_cost_le length.toNat inputLength.toNat nested) budget)
    watchedArray watchedCount watchedInput watchedLength watchedValid watchedBeforeFrame watchedBeforeArray finalValue run

#print axioms authorization_body_returned_whole_input_outer_prefix
end InitECandidate.Runtime
