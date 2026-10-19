import InitECandidate.Runtime.WitnessExtensionProgress
import InitECandidate.Runtime.NodeNewExtAlignedHeap
import InitECandidate.Runtime.WitnessExtensionStoresMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_extension_constructor_normal_heap_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap nib length child : BitVec 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      witnessExtensionArguments = some [.val (.word nib),.val (.word length),.val (.word child)])
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessExtensionConstructor = (none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
    heap.toNat≤(allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat≤33806089496 ∧
    (allocationEnd heap 56).toNat%8=0 ∧
    ∀ watched : BitVec 64, watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nib))).update
      (ofString "nlen",.val (.word length))).update (ofString "child",.val (.word child))
  let entry := callEntryStateHOLFinite s callee
  have atNib : entry.locals.lookup (ofString "nib") = some (.val (.word nib)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "child" ≠ ofString "nib" by decide,show ofString "nlen" ≠ ofString "nib" by decide]
  have atLength : entry.locals.lookup (ofString "nlen") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "child" ≠ ofString "nlen" by decide]
  have atChild : entry.locals.lookup (ofString "child") = some (.val (.word child)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have lookup := pan_three_word_lookup s.code.lookup (ofString "node_new_ext")
    (ofString "nib") (ofString "nlen") (ofString "child")
    (sourceFunctionBody Guest.guestFn_node_new_ext) nib length child (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_nodeNewExt_lookup)
  rw [source_witness_extension_constructor] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,readyLocals,readyMemory,readyGlobals,readyClock,
    readyDomain,readyEndian,readyCode,tailRun,postEq⟩ := evaluate_decCall_normal_global_memory_clock_scope
      s post (ofString "ex") (ofString "node_new_ext") .one .one witnessExtensionArguments
      [.val (.word nib),.val (.word length),.val (.word child)]
      (sourceFunctionBody Guest.guestFn_node_new_ext) witnessExtensionStores callee args lookup run
  obtain ⟨valueEq,heapPost,mono,cap,aligned,memory⟩ := node_new_ext_body_returned_aligned_heap_contract
    entry bodyPost heap nib length child atNib atLength atChild atHeap heapBound code value bodyRun
  subst value
  let tailState := setVarHOLFinite (ofString "ex") (.val (.word heap)) ready
  have atEx : tailState.locals.lookup (ofString "ex")=some (.val (.word heap)) := by
    simp [tailState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyMetadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_ext)
  rw [bodyRun] at bodyMetadata
  have tailGlobals := witness_extension_stores_globals_frame tailState (readyCode.trans (bodyMetadata.1.trans code))
  rw [tailRun] at tailGlobals
  refine ⟨?_,mono,cap,aligned,?_⟩
  · rw [postEq]
    change output.globals.lookup _=_
    rw [tailGlobals]
    change ready.globals.lookup _=_
    rw [readyGlobals]
    exact heapPost
  · intro watched before
    have tailMemory := witness_extension_stores_memory_below_heap tailState heap watched atEx heapBound before
    rw [tailRun] at tailMemory
    rw [postEq]
    change output.memory watched=s.memory watched
    exact tailMemory.trans ((congrFun readyMemory watched).trans (memory watched before))

#print axioms witness_extension_constructor_normal_heap_frame
end InitECandidate.Runtime
