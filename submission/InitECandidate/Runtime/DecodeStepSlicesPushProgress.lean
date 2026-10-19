import InitECandidate.Runtime.DecodeStepSlicesRuntimeReach
import InitECandidate.Runtime.DecodeStepListPushProgress
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned list-node push consumes a scratch record after the actual slice
construction, using its own table and restored workspace in the same execution. -/
theorem decode_step_slices_push_returned_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepListPushCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 4) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  have reached := decode_step_slices_runtime_reaches s pointer length consumed scratch frame array ceiling inputLimit
    atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by omega) heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 4) (decodeStepAt 5)
    _ _ _ reached (by rw [run])
  obtain ⟨count,atSlices,_,table,_,scratchReady,frameReady,_,_,_,codeReady,domainReady⟩ := facts
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 5) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    have progress := decode_step_array_push_returned_progress ready output array count pointer length scratch frame record
      ceiling inputLimit atSlices table lengthBound limitBound scratchReady frameReady (codeReady.trans code)
      orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      (by omega) tailRun
    have globals := agreement.2.2.2.1
    rw [run,tailRun] at globals
    change post.globals = output.globals at globals
    rw [globals]
    exact progress

#print axioms decode_step_slices_push_returned_progress
end InitECandidate.Runtime
