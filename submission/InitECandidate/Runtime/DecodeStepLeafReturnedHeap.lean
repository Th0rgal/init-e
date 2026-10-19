import InitECandidate.Runtime.NodeConstructorsReturnedHeap
import InitECandidate.Runtime.DecodeStepLeafBranchUniformBound
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.RlpItemBodyAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_leaf_stores_word_frame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (heap pointer length watched : BitVec 64)
    (atLeaf : s.locals.lookup (ofString "lf") = some (.val (.word heap)))
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (heapBound : heap.toNat ≤ 33806089496) (before : watched.toNat < heap.toNat) :
    (evaluateHOLFiniteState s decodeStepLeafStores).2.memory watched = s.memory watched := by
  have separate (offset : Nat) (inside : offset ≤ 16) : watched ≠ heap+BitVec.ofNat 64 offset := by
    intro same
    have addNat : (heap+BitVec.ofNat 64 offset).toNat = heap.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    have equal := congrArg BitVec.toNat same
    rw [addNat] at equal
    omega
  have supported : BoundWordStoreChainFrame (F := F) s.locals watched decodeStepLeafStores := by
    rw [source_decodeStep_leaf_stores]
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+8,?_,separate 8 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atLeaf,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨pointer,by simpa [evalHOLExact,locals,atPointer] using evaluated.symm⟩
    apply BoundWordStoreChainFrame.store
    · intro state locals
      refine ⟨heap+16,?_,separate 16 (by decide)⟩
      simp [evalHOLExact,evalListHOLExact,locals,atLeaf,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals parsed evaluated
      exact ⟨length,by simpa [evalHOLExact,locals,atLength] using evaluated.symm⟩
    exact .tail _ rfl
  exact evaluate_boundWordStoreChain_frame supported s rfl

theorem decode_step_leaf_construction_returned_heap_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap nibs count flag valueKind valuePointer valueLength consumed : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (atValue : s.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word valueKind),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepLeafConstruction = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 64))) ∧
      heap.toNat ≤ (allocationEnd heap 64).toNat ∧ (allocationEnd heap 64).toNat ≤ 33806089496 ∧
      (allocationEnd heap 64).toNat%8 = 0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((HolFiniteMapExact.empty.update (ofString "nib",.val (.word nibs))).update
      (ofString "nlen",.val (.word count))).update (ofString "vptr",.val (.word valuePointer))).update
      (ofString "vlen",.val (.word valueLength))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 0 (.var .local (ofString "cn")),.rfield 1 (.var .local (ofString "cn")),
       .rfield 1 (.var .local (ofString "vi")),.rfield 2 (.var .local (ofString "vi"))] =
      some [.val (.word nibs),.val (.word count),.val (.word valuePointer),.val (.word valueLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPath,atValue]
  have lookup := pan_four_word_lookup s.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen")
    (sourceFunctionBody Guest.guestFn_node_new_leaf) nibs count valuePointer valueLength
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_nodeNewLeaf_lookup)
  rw [source_decodeStep_leaf_construction] at run
  obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "lf") (ofString "node_new_leaf") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_node_new_leaf) decodeStepLeafStores callee value args lookup run
  have facts := node_new_leaf_body_returned_heap_contract entry bodyPost heap nibs count valuePointer valueLength
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE])
    atHeap heapBound code allocated bodyRun
  obtain ⟨rfl,heapPost,growth,capped,aligned,memory⟩ := facts
  let ready := setVarHOLFinite (ofString "lf") (.val (.word heap)) {bodyPost with locals := s.locals}
  have atLeaf : ready.locals.lookup (ofString "lf") = some (.val (.word heap)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have p : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "lf" ≠ ofString "p" by decide] using atPointer
  have n : ready.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "lf" ≠ ofString "n" by decide] using atLength
  have globalFrame : OriginalGlobalsFrame decodeStepLeafStores := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_decodeStep_leaf_stores]
    rfl
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_leaf)
  rw [bodyRun] at metadata
  have globals := globalFrame ready (metadata.1.trans code)
  rw [tailRun] at globals
  rw [postEq]
  refine ⟨?_,growth,capped,aligned,?_⟩
  · change output.globals.lookup _ = _
    rw [globals]
    exact heapPost
  · intro watched before
    have tailFrame := decode_step_leaf_stores_word_frame ready heap pointer length watched atLeaf p n heapBound before
    rw [tailRun] at tailFrame
    exact tailFrame.trans (memory watched before)

theorem decode_step_leaf_value_returned_heap {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap nibs count flag valueKind valuePointer valueLength consumed : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (atValue : s.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word valueKind),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepLeafValueContinuation = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 64))) ∧
      heap.toNat ≤ (allocationEnd heap 64).toNat ∧ (allocationEnd heap 64).toNat ≤ 33806089496 ∧
      (allocationEnd heap 64).toNat%8 = 0 ∧
      ∀ watched : BitVec 64, watched.toNat < heap.toNat → post.memory watched = s.memory watched := by
  rw [source_decodeStep_leaf_value_continuation] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 6 code normal
  subst next
  exact decode_step_leaf_construction_returned_heap_contract s post pointer length heap nibs count flag valueKind
    valuePointer valueLength consumed atPointer atLength atPath atValue atHeap heapBound code value tailRun

#print axioms decode_step_leaf_stores_word_frame
#print axioms decode_step_leaf_construction_returned_heap_contract
#print axioms decode_step_leaf_value_returned_heap
end InitECandidate.Runtime
