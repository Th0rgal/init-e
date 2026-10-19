import InitECandidate.Runtime.NodeNewHashedReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem node_new_hashed_body_returned_aligned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap hash : BitVec 64)
    (atHash : s.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_hashed) = (some (.returned value),post)) :
    value = .val (.word heap) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 32))) ∧
      heap.toNat ≤ (allocationEnd heap 32).toNat ∧ (allocationEnd heap 32).toNat ≤ 33806089496 ∧ (allocationEnd heap 32).toNat%8=0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  rw [source_nodeNewHashed_body] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "nd")
      (.const 32) nodeNewHashedStores heap 32 value (by rfl) code atHeap heapBound run
  have atNd : ready.locals.lookup (ofString "nd") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have hashReady : ready.locals.lookup (ofString "hash") = some (.val (.word hash)) := by
    rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nd" ≠ ofString "hash" by decide] using atHash
  have globalFrame : OriginalGlobalsFrame nodeNewHashedStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_nodeNewHashed_stores]
    rfl
  have kept := globalFrame ready (readyCode.trans code)
  rw [tailRun] at kept
  refine ⟨node_new_hashed_stores_returned_pointer ready output heap value atNd tailRun,?_,by omega,within,aligned,?_⟩
  · rw [postGlobals,kept,globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro watched before
    have separate : ∀ offset ∈ ([0,8,16,24] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset := by
      intro offset inside same
      have small : offset ≤ 24 := by simp at inside; omega
      have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      have equal := congrArg BitVec.toNat same
      rw [addNat] at equal
      omega
    have frame := node_new_hashed_stores_word_frame ready heap hash watched atNd hashReady separate
    rw [tailRun] at frame
    exact (congrFun postMemory watched).trans (frame.trans (congrFun memory watched))

#print axioms node_new_hashed_body_returned_aligned_heap_contract
end InitECandidate.Runtime
