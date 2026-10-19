import InitECandidate.Runtime.DecodeStepEntryPushProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Remaining persistent 88-byte decoder records in the actual scratch interval. -/
def scratchRecordCapacity (scratch frame : BitVec 64) : Nat :=
  (scratch.toNat - frame.toNat) / 88

def decoderScratchCapacity {F : Type} (frame : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.globals.lookup (ofString "scratch_ptr") with
  | some (.val (.word pointer)) => scratchRecordCapacity pointer frame
  | _ => 0

theorem scratchRecordCapacity_decreases (before after frame : BitVec 64)
    (lower : frame.toNat ≤ after.toNat) (spent : after.toNat + 88 ≤ before.toNat) :
    scratchRecordCapacity after frame < scratchRecordCapacity before frame := by
  unfold scratchRecordCapacity
  omega

/-- The capacity is uniformly finite even before the concrete arena bounds are
inserted by the caller. Successful pushes strictly decrease this actual capacity. -/
theorem scratchRecordCapacity_bounded (scratch frame : BitVec 64) :
    scratchRecordCapacity scratch frame ≤ (2^64-1)/88 := by
  unfold scratchRecordCapacity
  have limit := scratch.isLt
  omega

/-- The complete original decoder's returned push strictly decreases the number
of records available above the frame frontier, without assuming input shrinking. -/
theorem decode_step_entry_push_decreases_capacity {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepParseCost length.toNat + (decodeStepSlicesCost inputLimit + decodeStepListPushCost inputLimit) ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 0) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    decoderScratchCapacity frame post < decoderScratchCapacity frame s := by
  have progress := decode_step_entry_push_returned_progress s post pointer length scratch frame array record
    ceiling inputLimit atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run
  simp only [decoderScratchCapacity,scratchGlobal,progress.1]
  exact scratchRecordCapacity_decreases scratch (scratchAllocationEnd scratch 88) frame progress.2.1 progress.2.2

#print axioms scratchRecordCapacity_decreases
#print axioms scratchRecordCapacity_bounded
#print axioms decode_step_entry_push_decreases_capacity
end InitECandidate.Runtime
