import InitECandidate.Runtime.NodeNewExtBody
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.StoreChainReturnedLocal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_new_ext_stores_returned_pointer {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64) (value : ValueHOL 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState s nodeNewExtStores = (some (.returned value),post)) :
    value = .val (.word heap) := by
  apply evaluate_storeChain_returned_local (key := ofString "nd") _ s post heap value atNd run
  rw [source_nodeNewExt_stores]
  exact .store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ .finish))))))

theorem node_new_ext_stores_word_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap nib length child watched : BitVec 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (atNib : s.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (atLength : s.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (atChild : s.locals.lookup (ofString "child") = some (.val (.word child)))
    (separate : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState s nodeNewExtStores).2.memory watched = s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched nodeNewExtStores := by
    rw [source_nodeNewExt_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 0,?_,separate 0 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (2 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨2,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 8,?_,separate 8 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 16,?_,separate 16 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 24,?_,separate 24 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨0,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 32,?_,separate 32 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word nib) := by simpa [evalHOLExact,locals,atNib] using evaluated.symm
      exact ⟨nib,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 40,?_,separate 40 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word length) := by simpa [evalHOLExact,locals,atLength] using evaluated.symm
      exact ⟨length,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 48,?_,separate 48 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word child) := by simpa [evalHOLExact,locals,atChild] using evaluated.symm
      exact ⟨child,equal⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

theorem node_new_ext_body_returned_pointer_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap nib length child watched : BitVec 64)
    (atNib : s.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (atLength : s.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (atChild : s.locals.lookup (ofString "child") = some (.val (.word child)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (separate : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_ext) = (some (.returned value),post)) :
    value = .val (.word heap) ∧ post.memory watched = s.memory watched := by
  rw [source_nodeNewExt_body] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "nd")
      (.const 56) nodeNewExtStores heap 56 value (by rfl) code atHeap heapBound run
  have atNd : ready.locals.lookup (ofString "nd") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "nd" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have frame := node_new_ext_stores_word_frame ready heap nib length child watched atNd
    ((other _ (by decide)).trans atNib) ((other _ (by decide)).trans atLength)
    ((other _ (by decide)).trans atChild) separate
  rw [tailRun] at frame
  exact ⟨node_new_ext_stores_returned_pointer ready output heap value atNd tailRun,
    (congrFun postMemory watched).trans (frame.trans (congrFun memory watched))⟩

#print axioms node_new_ext_stores_returned_pointer
#print axioms node_new_ext_stores_word_frame
#print axioms node_new_ext_body_returned_pointer_frame
end InitECandidate.Runtime
