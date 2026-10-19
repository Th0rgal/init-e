import InitECandidate.Runtime.DecodeStepSlicesUniformBound
import InitECandidate.Runtime.DecodeStepNonemptyBytes
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The actual parsed RLP kind dispatch is bounded on every outcome, including
empty-node return and invalid byte-node rejection. -/
theorem runBounded_decode_step_kind {F : Type} (s : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (parsedKind : kind = 0 ∨ kind = 1)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) :
    RunBounded s (decodeStepAt 3) (decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit) := by
  rcases parsedKind with zero | list
  · subst kind
    by_cases empty : length = 0
    · subst length
      unfold RunBounded
      rw [evaluate_decode_step_empty_bytes s pointer consumed atItem]
      simp [emptyLocalsHOLFinite]
    · unfold RunBounded
      rw [evaluate_decode_step_nonempty_bytes s pointer length consumed empty code atItem]
      have minimum : 1 ≤ decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit := by
        unfold decodeStepTwoCaseCost
        omega
      have bounded := evaluate_mptFail_call_bounded s (.const 4) 4 code (by omega)
        (by rw [evalListHOLFinite_eq_toExact]; rfl)
      exact (show RunBounded s (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) 1 from
        ⟨by rw [bounded.1]; omega,by rw [bounded.1]; omega,bounded.2.1⟩).weaken minimum
  · subst kind
    unfold RunBounded
    rw [evaluate_decode_step_list_dispatch s pointer length consumed atItem]
    exact runBounded_decode_step_slices s pointer length consumed scratch frame array ceiling inputLimit
      atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap

#print axioms runBounded_decode_step_kind
end InitECandidate.Runtime
