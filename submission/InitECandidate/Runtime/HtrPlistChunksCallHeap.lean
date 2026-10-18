import InitECandidate.Runtime.HtrPlistChunksReturnedHeap
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrPlistChunks_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_plist_chunks") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_plist_chunks") =
      some ([(ofString "roots",.one),(ofString "n",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_plist_chunks,.one) := by
    rw [code]
    exact originalRuntimeCode_htr_plist_chunks_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "htr_plist_chunks") (ofString "roots") (ofString "n")
    (ofString "len") (ofString "out") (sourceFunctionBody Guest.guestFn_htr_plist_chunks) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_plist_chunks")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_plist_chunks) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((((HolFiniteMapExact.empty.update (ofString "roots",.val (.word pointer))).update
      (ofString "n",.val (.word n))).update (ofString "len",.val (.word limit))).update
      (ofString "out",.val (.word out)))
  exact htrPlistChunks_body_returned_heap entry bodyPost pointer n out heap value
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact atHeap) (by exact code) bodyRun

#print axioms htrPlistChunks_call_normal_heap
end InitECandidate.Runtime
