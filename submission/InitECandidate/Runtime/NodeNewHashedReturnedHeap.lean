import InitECandidate.Runtime.NodeNewHashedBody
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.StoreChainReturnedLocal
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_new_hashed_stores_returned_pointer {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64) (value : ValueHOL 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState s nodeNewHashedStores = (some (.returned value),post)) :
    value = .val (.word heap) := by
  apply evaluate_storeChain_returned_local (key := ofString "nd") _ s post heap value atNd run
  rw [source_nodeNewHashed_stores]
  exact .store _ _ (.store _ _ (.store _ _ (.store _ _ .finish)))

theorem node_new_hashed_stores_word_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap hash watched : BitVec 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (atHash : s.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (separate : ∀ offset ∈ ([0,8,16,24] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState s nodeNewHashedStores).2.memory watched = s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched nodeNewHashedStores := by
    rw [source_nodeNewHashed_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 0,?_,separate 0 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 8,?_,separate 8 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 16,?_,separate 16 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 24,?_,separate 24 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word hash) := by simpa [evalHOLExact,locals,atHash] using evaluated.symm
      exact ⟨hash,equal⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

/-- An actual returned hashed-node construction proves its real allocation
frontier and preserves all earlier memory without room/domain success premises. -/
theorem node_new_hashed_body_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap hash : BitVec 64)
    (atHash : s.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_hashed) = (some (.returned value),post)) :
    value = .val (.word heap) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 32))) ∧
      heap.toNat ≤ (allocationEnd heap 32).toNat ∧ (allocationEnd heap 32).toNat ≤ 33806089496 ∧
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
  refine ⟨node_new_hashed_stores_returned_pointer ready output heap value atNd tailRun,?_,by omega,within,?_⟩
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

#print axioms node_new_hashed_stores_returned_pointer
#print axioms node_new_hashed_stores_word_frame
#print axioms node_new_hashed_body_returned_heap_contract
end InitECandidate.Runtime
