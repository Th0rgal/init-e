import InitECandidate.Runtime.CompletedNodeEnvelope
import InitECandidate.Runtime.DecodeStepLeafReturnedHeap
import InitECandidate.Runtime.StoreChainReturnedPairLocal
import InitECandidate.Runtime.AllocationRoundNoWrap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem decode_step_leaf_construction_completed_node {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap nibs count flag valueKind valuePointer valueLength consumed : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (atValue : s.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word valueKind),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node : BitVec 64) (completed : value=.rStruct [.val (.word (0#64)),.val (.word node)])
    (run : evaluateHOLFiniteState s decodeStepLeafConstruction = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
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
  have supported : StoreChainReturnedPairLocal (ofString "lf") 0 decodeStepLeafStores := by
    rw [source_decodeStep_leaf_stores]
    exact .store _ _ (.store _ _ .finish)
  have same := evaluate_storeChain_returned_pair_local supported ready output heap value atLeaf tailRun
  rw [completed] at same
  have nodeEq : node=heap := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj (ValueHOL.rStruct.inj same)).2).1)
  subst node
  have covers := allocationEnd_covers_noWrap heap 64 (by change heap.toNat+64+7 < 2^64; omega)
  refine Or.inr ⟨allocationEnd heap 64,?_,Nat.le_refl _,by change heap.toNat+64 ≤ _ at covers; omega,capped⟩
  rw [postEq]
  change output.globals.lookup _ = _
  rw [globals]
  exact heapPost


theorem decode_step_leaf_value_completed_node {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (pointer length heap nibs count flag valueKind valuePointer valueLength consumed : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atPath : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word flag)]))
    (atValue : s.locals.lookup (ofString "vi") = some
      (.rStruct [.val (.word valueKind),.val (.word valuePointer),.val (.word valueLength),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node : BitVec 64) (completed : value=.rStruct [.val (.word (0#64)),.val (.word node)])
    (run : evaluateHOLFiniteState s decodeStepLeafValueContinuation = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  rw [source_decodeStep_leaf_value_continuation] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 6 code normal
  subst next
  exact decode_step_leaf_construction_completed_node s post pointer length heap nibs count flag valueKind
    valuePointer valueLength consumed atPointer atLength atPath atValue atHeap heapBound code value node completed tailRun

#print axioms decode_step_leaf_construction_completed_node
#print axioms decode_step_leaf_value_completed_node
end InitECandidate.Runtime
