import InitECandidate.Runtime.DecodeStepSlicesUniformBound
import InitECandidate.Runtime.DecodeStepArrayPlacedMetadata
import InitECandidate.Runtime.DecodeStepSlicesHeapReach
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem remainingBudget {a b initial remaining : Nat}
    (total : a+b ≤ initial) (spent : initial ≤ remaining+a) : b ≤ remaining := by omega

theorem decode_step_slices_push_returned_placed_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame array originalPointer originalLength : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word originalPointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word originalLength)))
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word consumed)]))
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
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (record : BitVec 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 4) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderPlacedPushedTable post record originalPointer originalLength pointer length ceiling array.toNat := by
  have reached := decode_step_slices_heap_reaches s pointer length consumed scratch frame array ceiling inputLimit
    atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    ((Nat.le_add_right _ _).trans budget) heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
  obtain ⟨next,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 4)
    (decodeStepAt 5) _ _ _ reached (by rw [run])
  cases tailRun : evaluateHOLFiniteState next (decodeStepAt 5) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    obtain ⟨count,atSlices,countBound,table,heapNext,scratchNext,frameNext,interval,endpoint,aligned,codeNext,domain,locals,memory⟩ := facts
    have sizeNat : (count * 16).toNat = count.toNat * 16 := by
      rw [BitVec.toNat_mul]
      change (count.toNat * 16) % 2^64 = count.toNat * 16
      exact Nat.mod_eq_of_lt (by omega)
    have covers := allocationEnd_covers array (count * 16) (by rw [sizeNat]; exact interval)
    rw [sizeNat] at covers
    have pointerNext : next.locals.lookup (ofString "p") = some (.val (.word originalPointer)) := by
      rw [locals]
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "sl" ≠ ofString "p" by decide] using atPointer
    have lengthNext : next.locals.lookup (ofString "n") = some (.val (.word originalLength)) := by
      rw [locals]
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "sl" ≠ ofString "n" by decide] using atLength
    have kept := decode_step_array_push_returned_placed_table next output array count pointer length (allocationEnd array (count * 16)) scratch frame originalPointer originalLength
      ceiling inputLimit pointerNext lengthNext atSlices table lengthBound limitCap heapNext endpoint aligned covers.1 arrayAbove
      scratchNext frameNext (codeNext.trans code) orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domain]; exact arena address lower upper) (remainingBudget budget spent) record tailRun
    have globals := agreement.2.2.2.1
    have finalMemory := agreement.2.2.1
    have finalDomain := agreement.2.2.2.2
    rw [run,tailRun] at globals finalMemory finalDomain
    exact kept.after_frame output post record originalPointer originalLength pointer length ceiling array.toNat finalMemory globals finalDomain

#print axioms decode_step_slices_push_returned_placed_table
end InitECandidate.Runtime
