import InitECandidate.Runtime.AccessListStepInputBound
import InitECandidate.Runtime.AccessListStepHeapRuntimeContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_step_input_heap_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index outerArray count input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word outerArray),.val (.word count)]))
    (valid : RlpSliceInputPrefix state outerArray input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    ∃ slotCount : BitVec 64, slotCount.toNat ≤ inputLength.toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat + 32 + slotCount.toNat * 48 ≤ (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ∧
      (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ≤ array.toNat + slotCount.toNat * 48 + 46 ∧
      (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat ≤ 33806089496 ∧ (allocationEnd (allocationEnd (allocationEnd array 32) (slotCount * 16)) (slotCount * 32)).toNat % 8 = 0 := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,starts,ends⟩ := rlpSliceInputPrefix_access_arguments state
    outerArray index count input inputLength count.toNat listLocal indexLocal valid inside
  have cost := accessStepCost_mono_left length.toNat inputLength.toNat inputLength.toNat lengthBound
  have contract := access_step_heap_runtime_contract state post pointer length input inputLength scratch frame array
    ceiling inputLimit args noWrap (Nat.le_trans lengthBound inputBound) inputBound limitBound
    starts ends scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    (Nat.le_trans ends inputBeforeFrame) (Nat.le_trans ends inputBeforeArray) arrayAbove inputBeforeArray inputBeforeFrame
    (Nat.le_trans cost budget) run
  exact contract

#print axioms access_step_input_heap_runtime_contract
theorem access_step_input_guarded_heap_bounds {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index outerArray count input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word outerArray),.val (.word count)]))
    (valid : RlpSliceInputPrefix state outerArray input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      array.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ array.toNat + inputLength.toNat * 48 + 46 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 := by
  obtain ⟨slotCount,slotBound,heapFinal,scratchFinal,frameFinal,low,high,endBound,endAligned⟩ :=
    access_step_input_heap_runtime_contract state post index outerArray count input inputLength scratch frame array ceiling inputLimit
      indexLocal listLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove budget run
  refine ⟨_,heapFinal,scratchFinal,frameFinal,?_,?_,endBound,endAligned⟩
  · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) low)
  · exact Nat.le_trans high (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right 48 slotBound) _) 46)

#print axioms access_step_input_guarded_heap_bounds
end InitECandidate.Runtime
