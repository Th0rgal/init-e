import InitECandidate.Runtime.BlobHashesBodyIndependentPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_mixed_body_cost_le (length whole : Nat) (bounded : length ≤ whole) :
    length * ((2 * length + 1) * 15 + 19) + length * 12 + 4 +
      (length * (whole * ((2 * whole + 1) * 15 + 19) + 92651) + 2) ≤ blobHashesBodyCost whole := by
  have factor : (2 * length + 1) * 15 + 19 ≤ (2 * whole + 1) * 15 + 19 := by omega
  have first := Nat.mul_le_mul bounded factor
  have bytes := Nat.mul_le_mul_right 12 bounded
  have iterations := Nat.mul_le_mul_right (whole * ((2 * whole + 1) * 15 + 19) + 92651) bounded
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add first bytes) 4) (Nat.add_le_add_right iterations 2)

/-- Whole-input budgets and reserves suffice for preservation by a nested blob payload. -/
theorem blobHashes_body_returned_whole_input_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (arrayBeforeFrame : array.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (budget : blobHashesBodyCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_blob_hashes) = (some (.returned finalValue),final)) :
    RlpSliceInputPrefix final watchedArray input inputLength watchedCount.toNat := by
  have nested : length.toNat ≤ inputLength.toNat := by omega
  exact blobHashes_body_returned_independent_prefix state final pointer length input inputLength scratch frame array ceiling inputLimit
    pointerLocal lengthLocal noWrap lengthBound inputBound starts ends limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
    (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 nested) _) arrayBeforeFrame) arrayAligned
    (Nat.le_trans (blobHashes_mixed_body_cost_le length.toNat inputLength.toNat nested) budget)
    watchedArray watchedCount watchedValid watchedBeforeFrame watchedBeforeArray finalValue run

#print axioms blobHashes_body_returned_whole_input_prefix
end InitECandidate.Runtime
