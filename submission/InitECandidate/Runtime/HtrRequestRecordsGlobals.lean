import InitECandidate.Runtime.HtrHeapGlobals
import InitECandidate.Runtime.HtrRequestRecordsReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem htrDeposit_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_deposit) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (htrU64At_call_globals _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrBytesVector_lookup
        (NormalRel.returned htrBytesVector_normal_heapGlobals)
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrDeposit_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_deposit") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrDeposit_lookup
    (NormalRel.returned htrDeposit_normal_heapGlobals)

theorem htrDeposit_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_deposit") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrDeposit_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrDeposit_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrDeposit_normal_heapGlobals
#print axioms htrDeposit_call_heapGlobals
#print axioms htrDeposit_call_normal_globals

theorem htrWdreq_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_wdreq) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (htrU64At_call_globals _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrBytesVector_lookup
        (NormalRel.returned htrBytesVector_normal_heapGlobals)
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrWdreq_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_wdreq") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrWdreq_lookup
    (NormalRel.returned htrWdreq_normal_heapGlobals)

theorem htrWdreq_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_wdreq") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrWdreq_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrWdreq_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrWdreq_normal_heapGlobals
#print axioms htrWdreq_call_heapGlobals
#print axioms htrWdreq_call_normal_globals

theorem htrCons_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_cons) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (htrU64At_call_globals _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrBytesVector_lookup
        (NormalRel.returned htrBytesVector_normal_heapGlobals)
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrCons_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_cons") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrCons_lookup
    (NormalRel.returned htrCons_normal_heapGlobals)

theorem htrCons_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_cons") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrCons_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrCons_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrCons_normal_heapGlobals
#print axioms htrCons_call_heapGlobals
#print axioms htrCons_call_normal_globals

theorem htrBdep_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_bdep) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (htrU64At_call_globals _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrBytesVector_lookup
        (NormalRel.returned htrBytesVector_normal_heapGlobals)
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrBdep_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_bdep") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrBdep_lookup
    (NormalRel.returned htrBdep_normal_heapGlobals)

theorem htrBdep_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bdep") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrBdep_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrBdep_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrBdep_normal_heapGlobals
#print axioms htrBdep_call_heapGlobals
#print axioms htrBdep_call_normal_globals

theorem htrBexit_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_bexit) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  repeat first
    | exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    | apply normalRel_seq pre
    | apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark
        (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
    | exact normalRel_of_frame pre (htrU64At_call_globals _)
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrBytesVector_lookup
        (NormalRel.returned htrBytesVector_normal_heapGlobals)
    | exact normalRel_of_frame pre (memcpy_call_globals_frame _)
    | exact merkleize_call_heapGlobals _
    | exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

theorem htrBexit_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_bexit") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrBexit_lookup
    (NormalRel.returned htrBexit_normal_heapGlobals)

theorem htrBexit_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bexit") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrBexit_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrBexit_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrBexit_normal_heapGlobals
#print axioms htrBexit_call_heapGlobals
#print axioms htrBexit_call_normal_globals

end InitECandidate.Runtime
