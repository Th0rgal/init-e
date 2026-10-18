import InitECandidate.Runtime.AuthorizationsStepInputIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsStepHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsStepArguments
import InitECandidate.Runtime.AuthorizationsStepCostMonotone
import InitECandidate.Runtime.AuthorizationsStepSource
import InitECandidate.Runtime.AuthorizationsItemCheckHeapBound
import InitECandidate.Runtime.AuthorizationsInnerCostMonotone
import InitECandidate.Runtime.RlpItemBodyRuntimeContract
import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
import InitECandidate.Runtime.AuthorizationsEntryCheckHeapBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BlobHashesDeclarationBound
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual authorization argument loads and writes retain a distinct earlier field array. -/
theorem authorization_step_input_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (record records index outerArray count input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (recordBeforeArray : record.toNat + 120 ≤ array.toNat) (recordFits : record.toNat + 120 < 2^64)
    (budget : authorizationStepCost inputLength.toNat inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (outerFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ watchedArray.toNat)
    (outerBeforeRecord : watchedArray.toNat + watchedCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationStep = (none,post)) :
    RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,starts,ends⟩ := rlpSliceInputPrefix_authorization_arguments state
    outerArray index count input inputLength count.toNat listLocal indexLocal valid inside
  have cost := authorizationStepCost_mono_left length.toNat inputLength.toNat inputLength.toNat lengthBound
  exact authorization_step_normal_heap_independent_outer_prefix state post record records index pointer length input inputLength scratch frame array
    watchedArray watchedCount watchedInput watchedLength ceiling inputLimit recordAddress recordsLocal indexLocal args noWrap (Nat.le_trans lengthBound inputBound) inputBound limitBound
    starts ends scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    (Nat.le_trans ends inputBeforeFrame) (Nat.le_trans ends inputBeforeArray) arrayAbove recordBeforeArray recordFits
    (Nat.le_trans cost budget) watchedValid outerFits outerAbove outerBeforeRecord run

#print axioms authorization_step_input_heap_independent_outer_prefix
end InitECandidate.Runtime
