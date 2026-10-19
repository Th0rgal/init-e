import InitECandidate.Runtime.HtrRequestRecordsCallBound
import InitECandidate.Runtime.RecordHashReturnedHeap
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrDeposit_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_deposit") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_deposit") =
      some ([(ofString "e",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_deposit,.one) := by
    rw [code]
    exact originalRuntimeCode_htrDeposit_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_deposit") (ofString "e")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_deposit) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_deposit")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_deposit) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word pointer))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural,source_htrDeposit_record] at bodyRun
  exact recordHash_body_returned_heap entry bodyPost (5#64) heap depositHashSteps value code atHeap bodyRun

#print axioms htrDeposit_call_normal_heap

theorem htrWdreq_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_wdreq") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_wdreq") =
      some ([(ofString "e",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_wdreq,.one) := by
    rw [code]
    exact originalRuntimeCode_htrWdreq_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_wdreq") (ofString "e")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_wdreq) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_wdreq")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_wdreq) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word pointer))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural,source_htrWdreq_record] at bodyRun
  exact recordHash_body_returned_heap entry bodyPost (3#64) heap wdreqHashSteps value code atHeap bodyRun

#print axioms htrWdreq_call_normal_heap

theorem htrCons_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_cons") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_cons") =
      some ([(ofString "e",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_cons,.one) := by
    rw [code]
    exact originalRuntimeCode_htrCons_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_cons") (ofString "e")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_cons) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_cons")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_cons) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word pointer))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural,source_htrCons_record] at bodyRun
  exact recordHash_body_returned_heap entry bodyPost (3#64) heap consHashSteps value code atHeap bodyRun

#print axioms htrCons_call_normal_heap

theorem htrBdep_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bdep") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_bdep") =
      some ([(ofString "e",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bdep,.one) := by
    rw [code]
    exact originalRuntimeCode_htrBdep_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_bdep") (ofString "e")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bdep) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bdep")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_bdep) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word pointer))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural,source_htrBdep_record] at bodyRun
  exact recordHash_body_returned_heap entry bodyPost (4#64) heap bdepHashSteps value code atHeap bodyRun

#print axioms htrBdep_call_normal_heap

theorem htrBexit_call_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (code : state.code = originalRuntimeCode)
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bexit") arguments) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
  have installed : state.code.lookup (ofString "htr_bexit") =
      some ([(ofString "e",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bexit,.one) := by
    rw [code]
    exact originalRuntimeCode_htrBexit_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_bexit") (ofString "e")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bexit) pointer out
    (by decide) installed
  obtain ⟨value,bodyPost,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bexit")
    .one arguments _ (sourceFunctionBody Guest.guestFn_htr_bexit) _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "e",.val (.word pointer))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural,source_htrBexit_record] at bodyRun
  exact recordHash_body_returned_heap entry bodyPost (2#64) heap bexitHashSteps value code atHeap bodyRun

#print axioms htrBexit_call_normal_heap

end InitECandidate.Runtime
