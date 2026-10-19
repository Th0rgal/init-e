import InitECandidate.Runtime.CompletedNodeEnvelope
import InitECandidate.Runtime.ResolveStepSuffixHeap
import InitECandidate.Runtime.AllocationRoundNoWrap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem resolve_step_hashed_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind key payload consumed heap : BitVec 64)
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node outLength outHash : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node),.val (.word outLength),.val (.word outHash)])
    (run : evaluateHOLFiniteState s resolveStepHashed = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "it"))] = some [.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atItem]
  have lookup := pan_single_word_lookup s.code.lookup (ofString "node_new_hashed") (ofString "hash")
    (sourceFunctionBody Guest.guestFn_node_new_hashed) key
    (by rw [code]; exact originalRuntimeCode_nodeNewHashed_lookup)
  rw [source_resolve_step_hashed] at run
  obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "hn") (ofString "node_new_hashed") .one .one
      _ _ (sourceFunctionBody Guest.guestFn_node_new_hashed) _
      (HolFiniteMapExact.empty.update (ofString "hash",.val (.word key))) value args lookup run
  have atHash : (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "hash",.val (.word key)))).locals.lookup
      (ofString "hash") = some (.val (.word key)) := by
    simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨rfl,heapPost,growth,capped,wordFrame⟩ := node_new_hashed_body_returned_heap_contract
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "hash",.val (.word key)))) bodyPost
    heap key atHash atHeap heapBound code returned bodyRun
  have metadata := evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "hash",.val (.word key))))
    (sourceFunctionBody Guest.guestFn_node_new_hashed)
  rw [bodyRun] at metadata
  have tailFrame := memoryFrame_leaf
    (.return (.rstruct [.const 0,.var .local (ofString "hn"),.const 0,.const 0])) rfl
    (setVarHOLFinite (ofString "hn") (.val (.word heap)) {bodyPost with locals := s.locals}) (metadata.1.trans code)
  rw [tailRun] at tailFrame
  have actual : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "hn") (.val (.word heap)) {bodyPost with locals := s.locals})
      (.return (.rstruct [.const 0,.var .local (ofString "hn"),.const 0,.const 0])) =
      (some (.returned (.rStruct [.val (.word (0#64)),.val (.word heap),.val (.word (0#64)),.val (.word (0#64))])),
        emptyLocalsHOLFinite (setVarHOLFinite (ofString "hn") (.val (.word heap)) {bodyPost with locals := s.locals})) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact]
  have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (tailRun.symm.trans actual)).1)
  rw [completed] at values
  have nodeEq := returned_four_node_eq node heap _ _ _ _ _ _ values
  subst node
  have covers : heap.toNat+32 ≤ (allocationEnd heap 32).toNat :=
    allocationEnd_covers_noWrap heap 32 (by change heap.toNat+32+7 < 2^64; omega)
  refine Or.inr ⟨allocationEnd heap 32,?_,Nat.le_refl _,covers,capped⟩
  rw [postEq]
  change output.globals.lookup _ = _
  rw [tailFrame.2]
  exact heapPost


theorem resolve_step_lookup_tail_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind key payload consumed found pointer length heap : BitVec 64)
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atResult : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node outLength outHash : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node),.val (.word outLength),.val (.word outHash)])
    (run : evaluateHOLFiniteState s resolveStepLookupTail = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  by_cases missing : found = 0
  · subst found
    have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) resolveStepHashed .skip) =
        evaluateHOLFiniteState s resolveStepHashed := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_resolve_step_lookup_tail,evaluateHOLFiniteState_seq_line780,branch] at run
    cases called : evaluateHOLFiniteState s resolveStepHashed with
    | mk result middle =>
      rw [called] at run
      have terminal := resolve_step_hashed_terminal s
      rw [called] at terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped =>
        exact resolve_step_hashed_completed_node s post kind key payload consumed heap
          atItem atHeap heapBound code value node outLength outHash completed (called.trans run)
  · have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) resolveStepHashed .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atResult,Compiler.Encoders.Asm.wordCmpHOL,
        show found ≠ 0#64 from missing,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_lookup_tail,evaluateHOLFiniteState_seq_line780,branch] at run
    have actual : evaluateHOLFiniteState s
        (.return (.rstruct [.const 1,.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r")),.rfield 1 (.var .local (ofString "it"))])) =
        (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word key)])),emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atResult,atItem,shapeOfHOLExact]
    dsimp only at run
    have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (run.symm.trans actual)).1)
    rw [completed] at values
    have impossible := returned_four_tag_eq (0#64) (1#64) _ _ _ _ _ _ values
    exact False.elim ((by decide : (0#64) ≠ (1#64)) impossible)


theorem resolve_step_lookup_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table kind key payload consumed heap : BitVec 64)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node outLength outHash : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node),.val (.word outLength),.val (.word outHash)])
    (run : evaluateHOLFiniteState s resolveStepLookup = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  let entry := callEntryStateHOLFinite s (nodedbLookupCallee table key)
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "db"),.rfield 1 (.var .local (ofString "it"))] =
      some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atTable,atItem]
  have lookup := lookup_nodedb_lookup_callee table key
  rw [← code] at lookup
  rw [source_resolve_step_lookup] at run
  obtain ⟨result,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "r") (ofString "nodedb_lookup")
      (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_nodedb_lookup) resolveStepLookupTail (nodedbLookupCallee table key)
      value args lookup run
  obtain ⟨found,pointer,length,rfl⟩ := value_three_words_of_checked_shape result checked.1
  have framed := nodedb_lookup_memoryFrame entry code
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_lookup)
  rw [bodyRun] at framed metadata
  have facts := resolve_step_lookup_tail_completed_node
    (setVarHOLFinite (ofString "r") (.rStruct [.val (.word found),.val (.word pointer),.val (.word length)])
      {bodyPost with locals := s.locals}) output kind key payload consumed found pointer length heap
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "r" ≠ ofString "it" by decide] using atItem)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change bodyPost.globals.lookup _ = _; rw [framed.2]; exact atHeap)
    heapBound (metadata.1.trans code) value node outLength outHash completed tailRun
  rw [postEq]
  exact facts


theorem resolve_step_string_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table kind key payload consumed heap : BitVec 64)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node outLength outHash : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node),.val (.word outLength),.val (.word outHash)])
    (run : evaluateHOLFiniteState s resolveStepStringBranch = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  by_cases empty : payload = 0
  · subst payload
    have actual : evaluateHOLFiniteState s resolveStepStringBranch =
        (some (.returned (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))])),
          emptyLocalsHOLFinite s) := by
      rw [source_resolve_step_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,evalListHOLExact,shapeOfHOLExact]
    have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (run.symm.trans actual)).1)
    rw [completed] at values
    exact Or.inl (returned_four_node_eq node 0 _ _ _ _ _ _ values)
  · have guard : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0))
          (.return (.rstruct [.const 0,.const 0,.const 0,.const 0])) .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
        show payload ≠ 0#64 from empty,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_string,evaluateHOLFiniteState_seq_line780,guard] at run
    obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
      (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
    have same := mpt_fail_guard_normal_state s next _ 10 code normal
    subst next
    exact resolve_step_lookup_completed_node s post table kind key payload consumed heap
      atTable atItem atHeap heapBound code value node outLength outHash completed tailRun

theorem resolve_step_kind_completed_node {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table kind key payload consumed heap : BitVec 64)
    (pointer length : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode) (value : ValueHOL 64)
    (node outLength outHash : BitVec 64)
    (completed : value=.rStruct [.val (.word (0#64)),.val (.word node),.val (.word outLength),.val (.word outHash)])
    (run : evaluateHOLFiniteState s (resolveStepAt 3) = (some (.returned value),post)) :
    CompletedNodeEnvelope post node heap.toNat := by
  by_cases zero : kind = 0
  · subst kind
    have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip) =
        evaluateHOLFiniteState s resolveStepStringBranch := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL]
    rw [source_resolve_step_kind,evaluateHOLFiniteState_seq_line780,branch] at run
    cases firstRun : evaluateHOLFiniteState s resolveStepStringBranch with
    | mk result middle =>
      rw [firstRun] at run
      have terminal := resolve_step_string_terminal s
      rw [firstRun] at terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some stopped =>
        exact resolve_step_string_completed_node s post table 0 key payload consumed heap
          atTable atItem atHeap heapBound code value node outLength outHash completed (firstRun.trans run)
  · have branch : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
        show kind ≠ 0#64 from zero,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_kind,evaluateHOLFiniteState_seq_line780,branch] at run
    have actual : evaluateHOLFiniteState s
        (.return (.rstruct [.const 1,.var .local (ofString "p"),.var .local (ofString "n"),.const 0])) =
        (some (.returned (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word (0#64))])),emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atPointer,atLength,shapeOfHOLExact]
    dsimp only at run
    have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (run.symm.trans actual)).1)
    rw [completed] at values
    have impossible := returned_four_tag_eq (0#64) (1#64) _ _ _ _ _ _ values
    exact False.elim ((by decide : (0#64) ≠ (1#64)) impossible)

#print axioms resolve_step_hashed_completed_node
#print axioms resolve_step_lookup_tail_completed_node
#print axioms resolve_step_lookup_completed_node
#print axioms resolve_step_string_completed_node
#print axioms resolve_step_kind_completed_node
end InitECandidate.Runtime
