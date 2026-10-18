import InitECandidate.Runtime.AccessListStepInputBound
import InitECandidate.Runtime.AccessListStepHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_step_input_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (watched watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watched watchedInput watchedLength watchedCount.toNat)
    (records : BitVec 64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (watchedAbove : ceiling ≤ watched.toNat)
    (outerBeforeArray : watched.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (outerBeforeRecord : watched.toNat + watchedCount.toNat * 16 ≤ (records + index * 24#64).toNat)
    (recordFits : (records + index * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    RlpSliceInputPrefix post watched watchedInput watchedLength watchedCount.toNat := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,starts,ends⟩ := rlpSliceInputPrefix_access_arguments state
    outerArray index count input inputLength count.toNat listLocal indexLocal valid inside
  have cost := accessStepCost_mono_left length.toNat inputLength.toNat inputLength.toNat lengthBound
  exact access_step_heap_independent_outer_prefix state post pointer length input inputLength scratch frame array
    ceiling inputLimit args noWrap (Nat.le_trans lengthBound inputBound) inputBound limitBound
    starts ends scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    (Nat.le_trans ends inputBeforeFrame) (Nat.le_trans ends inputBeforeArray) inputBeforeArray inputBeforeFrame
    (Nat.le_trans cost budget) watched watchedCount watchedInput watchedLength records index watchedValid watchedAbove outerBeforeArray recordsLocal indexLocal
    outerBeforeRecord recordFits run

#print axioms access_step_input_heap_independent_outer_prefix
end InitECandidate.Runtime
