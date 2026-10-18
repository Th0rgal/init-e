import InitECandidate.Runtime.AccessListStepInputBound
import InitECandidate.Runtime.AccessListStepOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_step_input_independent_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (reserve : array.toNat + inputLength.toNat * 32 + 7 ≤ frame.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (records : BitVec 64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (watchedArray watchedCount : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray input inputLength watchedCount.toNat)
    (outerBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeArray : watchedArray.toNat + watchedCount.toNat * 16 ≤ array.toNat)
    (outerBeforeRecord : watchedArray.toNat + watchedCount.toNat * 16 ≤ (records + index * 24#64).toNat)
    (recordFits : (records + index * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessStep = (none,post)) :
    RlpSliceInputPrefix post watchedArray input inputLength watchedCount.toNat := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,starts,ends⟩ := rlpSliceInputPrefix_access_arguments state
    outerArray index count input inputLength count.toNat listLocal indexLocal valid inside
  have cost := accessStepCost_mono_left length.toNat inputLength.toNat inputLength.toNat lengthBound
  exact access_step_outer_prefix state post pointer length input inputLength scratch frame array
    ceiling inputLimit args noWrap (Nat.le_trans lengthBound inputBound) inputBound limitBound
    starts ends scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    (by omega) (Nat.le_trans ends inputBeforeArray) arrayBeforeFrame inputBeforeArray reserve
    (Nat.le_trans cost budget) watchedArray watchedCount records index watchedValid outerBeforeFrame outerBeforeArray recordsLocal indexLocal
    outerBeforeRecord recordFits run

#print axioms access_step_input_independent_prefix
end InitECandidate.Runtime
