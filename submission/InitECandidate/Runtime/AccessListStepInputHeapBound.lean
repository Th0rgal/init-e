import InitECandidate.Runtime.AccessListStepInputBound
import InitECandidate.Runtime.AccessListStepHeapBound
import InitECandidate.Runtime.AccessListStepArguments
import InitECandidate.Runtime.AuthorizationsStepArguments
import InitECandidate.Runtime.AuthorizationsStepCostMonotone
import InitECandidate.Runtime.AuthorizationsStepSource
import InitECandidate.Runtime.AuthorizationsItemCheckBound
import InitECandidate.Runtime.AuthorizationsInnerCostMonotone
import InitECandidate.Runtime.RlpItemBodyRuntimeContract
import InitECandidate.Runtime.RlpItemBodyBound
import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
import InitECandidate.Runtime.AuthorizationsEntryCheckBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BlobHashesDeclarationBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_access_step_input_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : accessStepCost inputLength.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessStep
    state.clock ≤ evaluated.2.clock + accessStepCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨pointer,length,args,noWrap,lengthBound,starts,ends⟩ := rlpSliceInputPrefix_access_arguments state
    outerArray index count input inputLength count.toNat listLocal indexLocal valid inside
  have cost := accessStepCost_mono_left length.toNat inputLength.toNat inputLength.toNat lengthBound
  have bounded := evaluate_access_step_heap_bounded state pointer length input inputLength scratch frame array
    ceiling inputLimit args noWrap (Nat.le_trans lengthBound inputBound) inputBound limitBound
    starts ends scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    (by omega) (Nat.le_trans ends inputBeforeArray) arrayAbove inputBeforeArray inputBeforeFrame
    (Nat.le_trans cost budget)
  exact ⟨Nat.le_trans bounded.1 (Nat.add_le_add_left cost _),bounded.2⟩

#print axioms evaluate_access_step_input_heap_bounded
end InitECandidate.Runtime
