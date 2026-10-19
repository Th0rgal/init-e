import InitECandidate.Runtime.DecodeStepArrayUniformBound
import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original list-to-slices allocation, array binding and every node arity have
one all-outcome bound. The successful runtime prefix supplies actual table
contents and heap geometry; failure requires no reserve assumption. -/
theorem runBounded_decode_step_slices {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
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
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) :
    RunBounded s (decodeStepAt 4) (decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit) := by
  have reached := decode_step_slices_runtime_reaches s pointer length consumed scratch frame array ceiling inputLimit
    atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    ((Nat.le_add_right _ _).trans budget) heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
  apply RunBounded.ofReaches budget reached
  intro next facts ticks
  obtain ⟨count,atSlices,countBound,table,heapNext,scratchNext,frameNext,interval,endpoint,aligned,codeNext,domain⟩ := facts
  have sizeNat : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul]
    change (count.toNat * 16) % 2^64 = count.toNat * 16
    exact Nat.mod_eq_of_lt (by omega)
  have covers := allocationEnd_covers array (count * 16) (by rw [sizeNat]; exact interval)
  rw [sizeNat] at covers
  exact runBounded_decode_step_array next array count pointer length (allocationEnd array (count * 16)) scratch frame
    ceiling inputLimit atSlices table lengthBound limitCap heapNext endpoint aligned covers.1 arrayAbove
    scratchNext frameNext (codeNext.trans code) orderedFrame framePositive scratchBelow
    (by intro address lower upper; rw [domain]; exact arena address lower upper) ticks

#print axioms runBounded_decode_step_slices
end InitECandidate.Runtime
