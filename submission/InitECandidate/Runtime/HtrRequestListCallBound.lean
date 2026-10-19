import InitECandidate.Runtime.HtrRequestListReturnedHeap
import InitECandidate.Runtime.OriginalHtrRequestListCode
import InitECandidate.Runtime.PanFiveWordShapeLookup
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def requestListParams (kind pointer count size out : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((((HolFiniteMapExact.empty.update (ofString "kind",.val (.word kind))).update
    (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word count))).update
    (ofString "sz",.val (.word size))).update (ofString "out",.val (.word out))

theorem htrRequestList_installed {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer count size out : BitVec 64) (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htr_request_list")
      [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)] =
      some (sourceFunctionBody Guest.guestFn_htr_request_list,requestListParams kind pointer count size out,.one) := by
  exact pan_five_word_shape_lookup state.code.lookup (ofString "htr_request_list") (ofString "kind") (ofString "p")
    (ofString "n") (ofString "sz") (ofString "out") (sourceFunctionBody Guest.guestFn_htr_request_list) .one
    kind pointer count size out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_htrRequestList_lookup)

theorem runBounded_htrRequestList_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (kind pointer count size out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)])
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrRequestListBodyCost count + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_request_list") arguments) (htrRequestListBodyCost count + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htrRequestList_installed state kind pointer count size out code] at lookup
  cases lookup
  apply runBounded_htrRequestList_body _ kind pointer size count out heap
  · constructor <;> simp (config := {decide := true}) [requestListParams,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact hh
  · exact small
  · exact cap
  · exact code
  · change htrRequestListBodyCost count ≤ state.clock - 1
    omega

theorem htrRequestList_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (kind pointer count size out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word kind),.val (.word pointer),.val (.word count),.val (.word size),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_request_list") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have lookup := htrRequestList_installed state kind pointer count size out code
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_request_list")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_request_list) _ args lookup run
  rw [postEq]
  exact htrRequestList_body_returned_heap (callEntryStateHOLFinite state (requestListParams kind pointer count size out))
    bodyPost heap value code atHeap bodyRun

#print axioms htrRequestList_installed
#print axioms runBounded_htrRequestList_call
#print axioms htrRequestList_call_normal_heap
end InitECandidate.Runtime
