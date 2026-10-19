import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.NodeNewExtReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem node_new_ext_body_returned_aligned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap nib length child : BitVec 64)
    (atNib : s.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (atLength : s.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (atChild : s.locals.lookup (ofString "child") = some (.val (.word child)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_ext) = (some (.returned value),post)) :
    value = .val (.word heap) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 56))) ∧
      heap.toNat ≤ (allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat ≤ 33806089496 ∧ (allocationEnd heap 56).toNat%8=0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  rw [source_nodeNewExt_body] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "nd")
      (.const 56) nodeNewExtStores heap 56 value (by rfl) code atHeap heapBound run
  have atNd : ready.locals.lookup (ofString "nd") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "nd" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalFrame : OriginalGlobalsFrame nodeNewExtStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_nodeNewExt_stores]
    rfl
  have kept := globalFrame ready (readyCode.trans code)
  rw [tailRun] at kept
  refine ⟨node_new_ext_stores_returned_pointer ready output heap value atNd tailRun,?_,by omega,within,aligned,?_⟩
  · rw [postGlobals,kept,globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro watched before
    have separate : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset := by
      intro offset inside same
      have small : offset ≤ 48 := by simp at inside; omega
      have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      have equal := congrArg BitVec.toNat same
      rw [addNat] at equal
      omega
    have frame := node_new_ext_stores_word_frame ready heap nib length child watched atNd
      ((other _ (by decide)).trans atNib) ((other _ (by decide)).trans atLength)
      ((other _ (by decide)).trans atChild) separate
    rw [tailRun] at frame
    exact (congrFun postMemory watched).trans (frame.trans (congrFun memory watched))

#print axioms node_new_ext_body_returned_aligned_heap_contract
end InitECandidate.Runtime
