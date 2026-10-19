import InitECandidate.Runtime.HtrPayloadReturnedHeap
import InitECandidate.Runtime.HtrPcontainerGlobals
import InitECandidate.Runtime.HtrWithdrawalGlobals
import InitECandidate.Runtime.HtrBytesVectorGlobals
import InitECandidate.Runtime.HtrBytesListGlobals
import InitECandidate.Runtime.HtrU64AtBound
import InitECandidate.Runtime.NormalRelLocalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- All continuing paths of the original payload body preserve non-heap
globals, including both ranked loops and the assigning withdrawal allocation. -/
theorem htrPayload_normal_heapGlobals : NormalRel HeapGlobalsRel (sourceFunctionBody Guest.guestFn_htr_payload) := by
  have pre := heapGlobalsRel_preorder
  rw [sourceFunctionBody_eq_structural]
  apply normalRel_dec pre
  apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
  apply normalRel_seq pre
  ·
    exact normalRel_of_frame pre (memcpy_call_globals_frame _)
  ·
    apply normalRel_seq pre
    ·
      exact htrBytesVector_call_heapGlobals _
    ·
      apply normalRel_seq pre
      ·
        exact normalRel_of_frame pre (memcpy_call_globals_frame _)
      ·
        apply normalRel_seq pre
        ·
          exact normalRel_of_frame pre (memcpy_call_globals_frame _)
        ·
          apply normalRel_seq pre
          ·
            exact htrBytesVector_call_heapGlobals _
          ·
            apply normalRel_seq pre
            ·
              exact normalRel_of_frame pre (memcpy_call_globals_frame _)
            ·
              apply normalRel_seq pre
              ·
                exact normalRel_of_frame pre (htrU64At_call_globals _)
              ·
                apply normalRel_seq pre
                ·
                  exact normalRel_of_frame pre (htrU64At_call_globals _)
                ·
                  apply normalRel_seq pre
                  ·
                    exact normalRel_of_frame pre (htrU64At_call_globals _)
                  ·
                    apply normalRel_seq pre
                    ·
                      exact normalRel_of_frame pre (htrU64At_call_globals _)
                    ·
                      apply normalRel_seq pre
                      ·
                        exact htrBytesList_call_heapGlobals _
                      ·
                        apply normalRel_seq pre
                        ·
                          exact normalRel_of_frame pre (memcpy_call_globals_frame _)
                        ·
                          apply normalRel_seq pre
                          ·
                            exact normalRel_of_frame pre (memcpy_call_globals_frame _)
                          ·
                            apply normalRel_dec pre
                            apply normalRel_dec pre
                            apply normalRel_decCall pre _ _ _ _ _ _ _ vmLookup_heap_mark (NormalRel.returned (normalRel_readOnly pre heapMark_readOnly))
                            apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
                            apply normalRel_dec pre
                            apply normalRel_seq pre
                            ·
                              apply normalRel_while pre
                              apply normalRel_seq pre
                              ·
                                exact htrPbytes_call_heapGlobals _
                              ·
                                exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
                            ·
                              apply normalRel_seq pre
                              ·
                                exact htrPlistChunks_call_heapGlobals _
                              ·
                                apply normalRel_seq pre
                                ·
                                  exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals
                                ·
                                  apply normalRel_dec pre
                                  apply normalRel_dec pre
                                  apply normalRel_seq pre
                                  ·
                                    exact normalRel_local_call pre _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returned_heapGlobals
                                  ·
                                    apply normalRel_seq pre
                                    ·
                                      exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
                                    ·
                                      apply normalRel_seq pre
                                      ·
                                        apply normalRel_while pre
                                        apply normalRel_seq pre
                                        ·
                                          exact htrWithdrawal_call_heapGlobals _
                                        ·
                                          exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))
                                      ·
                                        apply normalRel_seq pre
                                        ·
                                          exact htrPlistChunks_call_heapGlobals _
                                        ·
                                          apply normalRel_seq pre
                                          ·
                                            exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals
                                          ·
                                            apply normalRel_seq pre
                                            ·
                                              exact normalRel_of_frame pre (htrU64At_call_globals _)
                                            ·
                                              apply normalRel_seq pre
                                              ·
                                                exact normalRel_of_frame pre (htrU64At_call_globals _)
                                              ·
                                                apply normalRel_seq pre
                                                ·
                                                  exact htrPbytes_call_heapGlobals _
                                                ·
                                                  apply normalRel_seq pre
                                                  ·
                                                    exact normalRel_of_frame pre (htrU64At_call_globals _)
                                                  ·
                                                    apply normalRel_seq pre
                                                    ·
                                                      exact htrPcontainer_call_heapGlobals _
                                                    ·
                                                      apply normalRel_seq pre
                                                      ·
                                                        exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals
                                                      ·
                                                        exact normalRel_of_frame pre (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem htrPayload_call_heapGlobals (arguments : List (ExpHOL 64)) :
    NormalRel HeapGlobalsRel (.call (some (none,none)) (ofString "htr_payload") arguments) :=
  normalRel_discard_call heapGlobalsRel_preorder _ _ _ _ _ originalRuntimeCode_htrPayload_lookup
    (NormalRel.returned htrPayload_normal_heapGlobals)

/-- A normally returned original payload call restores the whole global map. -/
theorem htrPayload_call_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word out)])
    (atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_payload") arguments) = (none,post)) :
    post.globals = state.globals := by
  have frame := normalRel_apply (htrPayload_call_heapGlobals arguments)
    (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have restored := htrPayload_call_normal_heap state post arguments pointer out heap args code atHeap run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    exact restored.trans atHeap.symm
  · exact frame name same

#print axioms htrPayload_normal_heapGlobals
#print axioms htrPayload_call_heapGlobals
#print axioms htrPayload_call_normal_globals
end InitECandidate.Runtime
