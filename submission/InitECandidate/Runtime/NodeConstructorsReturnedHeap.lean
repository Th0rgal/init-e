import InitECandidate.Runtime.NodeNewLeafBody
import InitECandidate.Runtime.NodeNewBranchBody
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.BoundWordStoreChainFrame
import InitECandidate.Runtime.StoreChainReturnedLocal
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_new_leaf_stores_returned_pointer {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64) (value : ValueHOL 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (run : evaluateHOLFiniteState s nodeNewLeafStores = (some (.returned value),post)) :
    value = .val (.word heap) := by
  apply evaluate_storeChain_returned_local (key := ofString "nd") _ s post heap value atNd run
  rw [source_nodeNewLeaf_stores]
  exact .store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ (.store _ _ .finish)))))))

theorem node_new_leaf_stores_word_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap nib nlen vptr vlen watched : BitVec 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (at_nib : s.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (at_nlen : s.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (at_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word vptr)))
    (at_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word vlen)))
    (separate : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState s nodeNewLeafStores).2.memory watched = s.memory watched := by
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched nodeNewLeafStores := by
    rw [source_nodeNewLeaf_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 0,?_,separate 0 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word (1 : BitVec 64)) := by simpa [evalHOLExact] using evaluated.symm
      exact ⟨1,equal⟩
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
      have equal : parsed = .val (.word nib) := by simpa [evalHOLExact,locals,at_nib] using evaluated.symm
      exact ⟨nib,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 40,?_,separate 40 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word nlen) := by simpa [evalHOLExact,locals,at_nlen] using evaluated.symm
      exact ⟨nlen,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 48,?_,separate 48 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word vptr) := by simpa [evalHOLExact,locals,at_vptr] using evaluated.symm
      exact ⟨vptr,equal⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap + 56,?_,separate 56 (by simp)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atNd,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      have equal : parsed = .val (.word vlen) := by simpa [evalHOLExact,locals,at_vlen] using evaluated.symm
      exact ⟨vlen,equal⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

theorem node_new_leaf_body_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap nib nlen vptr vlen : BitVec 64)
    (at_nib : s.locals.lookup (ofString "nib") = some (.val (.word nib)))
    (at_nlen : s.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (at_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word vptr)))
    (at_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word vlen)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_leaf) = (some (.returned value),post)) :
    value = .val (.word heap) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 64))) ∧
      heap.toNat ≤ (allocationEnd heap 64).toNat ∧ (allocationEnd heap 64).toNat ≤ 33806089496 ∧
      (allocationEnd heap 64).toNat % 8 = 0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  rw [source_nodeNewLeaf_body] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,aligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "nd")
      (.const 64) nodeNewLeafStores heap 64 value (by rfl) code atHeap heapBound run
  have atNd : ready.locals.lookup (ofString "nd") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "nd" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have globalFrame : OriginalGlobalsFrame nodeNewLeafStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_nodeNewLeaf_stores]
    rfl
  have kept := globalFrame ready (readyCode.trans code)
  rw [tailRun] at kept
  refine ⟨node_new_leaf_stores_returned_pointer ready output heap value atNd tailRun,?_,by omega,within,aligned,?_⟩
  · rw [postGlobals,kept,globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro watched before
    have separate : ∀ offset ∈ ([0,8,16,24,32,40,48,56] : List Nat), watched ≠ heap + BitVec.ofNat 64 offset := by
      intro offset inside same
      have small : offset ≤ 56 := by simp at inside; omega
      have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
        rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
      have equal := congrArg BitVec.toNat same
      rw [addNat] at equal
      omega
    have frame := node_new_leaf_stores_word_frame ready heap nib nlen vptr vlen watched atNd
      ((other _ (by decide)).trans at_nib) ((other _ (by decide)).trans at_nlen)
      ((other _ (by decide)).trans at_vptr) ((other _ (by decide)).trans at_vlen) separate
    rw [tailRun] at frame
    exact (congrFun postMemory watched).trans (frame.trans (congrFun memory watched))

theorem node_new_branch_initialize_globals_frame : OriginalGlobalsFrame nodeNewBranchInitialize := by
  rw [source_nodeNewBranch_initialize]
  exact originalGlobalsFrame_sequence _ _ (memzero_call_globals_frame _)
    (originalGlobalsFrame_leaf _ (by intro watched; rfl))

/-- Actual returned branch initialization frames the older heap even when the
caller supplies no accessibility or zeroing-success hypotheses. -/
theorem node_new_branch_initialize_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64)
    (atNd : s.locals.lookup (ofString "nd") = some (.val (.word heap)))
    (bounded : heap.toNat+176 ≤ 33806089496) (aligned : heap.toNat%8 = 0)
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s nodeNewBranchInitialize = (some (.returned value),post)) :
    value = .val (.word heap) ∧ ∀ watched : BitVec 64, watched.toNat < heap.toNat →
      post.memory watched = s.memory watched := by
  rw [source_nodeNewBranch_initialize] at run
  obtain ⟨zeroed,zeroRun,tailRun⟩ := seq_returned_of_nonreturning_first
    (evaluate_discard_call_no_return s (ofString "memzero") _) run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "nd"),.const 176] = some [.val (.word heap),.val (.word (176#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNd]
  have locals := evaluate_discard_call_success_locals s (ofString "memzero") _ (congrArg Prod.fst zeroRun)
  rw [zeroRun] at locals
  have atNdZero : zeroed.locals.lookup (ofString "nd") = some (.val (.word heap)) := by rw [locals]; exact atNd
  have pointer := evaluate_storeChain_returned_local (key := ofString "nd") (.store _ _ .finish)
    zeroed post heap value atNdZero tailRun
  refine ⟨pointer,?_⟩
  intro watched before
  have zeroFrame := (memzero_call_normal_memory s zeroed _ heap 176 watched args code aligned bounded (Or.inl before) zeroRun).1
  have supported : BoundWordStoreChainFrame (F := F) zeroed.locals watched
      (.seq (.store (.op .add [.var .local (ofString "nd"),.const 0]) (.const 3))
        (.return (.var .local (ofString "nd")))) := by
    apply BoundWordStoreChainFrame.store
    · intro state bindings
      refine ⟨heap,?_,?_⟩
      · simp [evalHOLExact,evalListHOLExact,bindings,atNdZero,wordOpHOL,wordOp,valueIsWord,valueWord]
      · intro same; subst watched; omega
    · intro state bindings parsed evaluated
      exact ⟨3,by simpa [evalHOLExact] using evaluated.symm⟩
    · exact .tail _ rfl
  have tailFrame := evaluate_boundWordStoreChain_frame supported zeroed rfl
  rw [tailRun] at tailFrame
  exact tailFrame.trans zeroFrame

/-- Actual returned branch allocation certifies a fresh heap interval and its
aligned bounded endpoint; old heap preservation uses real returned memzero. -/
theorem node_new_branch_body_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap : BitVec 64)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat%8 = 0)
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_branch) = (some (.returned value),post)) :
    value = .val (.word heap) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 176))) ∧
      heap.toNat ≤ (allocationEnd heap 176).toNat ∧ (allocationEnd heap 176).toNat ≤ 33806089496 ∧
      (allocationEnd heap 176).toNat%8 = 0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  rw [source_nodeNewBranch_body] at run
  obtain ⟨ready,output,tailRun,locals,memory,readyCode,domain,globals,within,covers,endAligned,
    postMemory,postGlobals,postDomain⟩ := allocation_declaration_returned s post (ofString "nd")
      (.const 176) nodeNewBranchInitialize heap 176 value (by rfl) code atHeap heapBound run
  have atNd : ready.locals.lookup (ofString "nd") = some (.val (.word heap)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded : heap.toNat+176 ≤ 33806089496 := by change heap.toNat+176 ≤ _ at covers; omega
  have frame := node_new_branch_initialize_returned_frame ready output heap atNd bounded aligned (readyCode.trans code) value tailRun
  have kept := node_new_branch_initialize_globals_frame ready (readyCode.trans code)
  rw [tailRun] at kept
  refine ⟨frame.1,?_,by omega,within,endAligned,?_⟩
  · rw [postGlobals,kept,globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro watched before
    exact (congrFun postMemory watched).trans ((frame.2 watched before).trans (congrFun memory watched))

#print axioms node_new_leaf_stores_returned_pointer
#print axioms node_new_leaf_stores_word_frame
#print axioms node_new_leaf_body_returned_heap_contract
#print axioms node_new_branch_initialize_globals_frame
#print axioms node_new_branch_initialize_returned_frame
#print axioms node_new_branch_body_returned_heap_contract
end InitECandidate.Runtime
