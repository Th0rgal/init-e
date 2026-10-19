import InitECandidate.Runtime.WitnessExtensionStoresProgress
import InitECandidate.Runtime.NodeNewExtReturnedFrame
import InitECandidate.Runtime.OriginalNodeNewExtCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanDecCallNormalGlobalMemoryClockScope
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_extension_constructor_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev nib length child : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      witnessExtensionArguments = some [.val (.word nib),.val (.word length),.val (.word child)])
    (prevCell : s.memory top = .word prev)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessExtensionConstructor = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
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
  have separate : ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat), top ≠ heap + BitVec.ofNat 64 offset := by
    intro offset inside same
    have small : offset ≤ 48 := by simp at inside; omega
    have addNat : (heap + BitVec.ofNat 64 offset).toNat = heap.toNat + offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    have equal := congrArg BitVec.toNat same
    rw [addNat] at equal
    omega
  have framed := node_new_ext_body_returned_pointer_frame entry bodyPost heap nib length child top
    atNib atLength atChild atHeap heapBound code separate value bodyRun
  obtain ⟨rfl,wordFrame⟩ := framed
  have tailFacts := witness_extension_stores_normal_progress
    (setVarHOLFinite (ofString "ex") (.val (.word heap)) ready) output top heap prev
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,readyLocals,
      show ofString "ex" ≠ ofString "top" by decide] using atTop)
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change ready.memory top = _; rw [readyMemory,wordFrame]; exact prevCell)
    before heapBound tailRun
  rw [postEq]
  refine ⟨?_,?_,?_,tailFacts.2.2.2.trans ?_⟩
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact tailFacts.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact tailFacts.2.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide),tailFacts.2.2.1]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,readyLocals,
      show ofString "ex" ≠ ofString "mode" by decide]
  · change ready.memory top = s.memory top
    exact (congrFun readyMemory top).trans wordFrame

/-- A normal actual constructor declaration forces both source one-word loads
to have produced words; accessibility is derived from the actual run. -/
theorem witness_extension_constructor_normal_arguments {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (child : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word child)))
    (run : evaluateHOLFiniteState s witnessExtensionConstructor = (none,post)) :
    ∃ nib length : BitVec 64,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) witnessExtensionArguments =
        some [.val (.word nib),.val (.word length),.val (.word child)] := by
  have first : ∃ nib : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 64])) = some (.val (.word nib)) := by
    cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 64])) with
    | none =>
      rw [source_witness_extension_constructor,evaluateHOLFiniteState_decCall_total] at run
      simp only [evalListHOLFinite,witnessExtensionArguments,evalListHOLExact] at run
      rw [evaluated] at run
      cases run
    | some value =>
      obtain ⟨word,rfl⟩ := eval_load_one_word s _ value evaluated
      exact ⟨word,rfl⟩
  obtain ⟨nib,first⟩ := first
  have second : ∃ length : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 72])) = some (.val (.word length)) := by
    cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "top"),.const 72])) with
    | none =>
      rw [source_witness_extension_constructor,evaluateHOLFiniteState_decCall_total] at run
      simp only [evalListHOLFinite,witnessExtensionArguments,evalListHOLExact] at run
      rw [first,evaluated] at run
      cases run
    | some value =>
      obtain ⟨word,rfl⟩ := eval_load_one_word s _ value evaluated
      exact ⟨word,rfl⟩
  obtain ⟨length,second⟩ := second
  refine ⟨nib,length,?_⟩
  simp only [evalListHOLFinite,witnessExtensionArguments,evalListHOLExact]
  rw [first,second]
  simp [evalHOLExact,atResult]

/-- Actual normally completed extension unwind pops the original previous
activation and delivers the fresh heap parent. Neither loaded-byte domains,
constructor success, allocator room nor any clock premise is assumed. -/
theorem witness_extension_normal_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (top heap prev child : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word child)))
    (prevCell : s.memory top = .word prev)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (before : top.toNat < heap.toNat) (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindExtension = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode") = s.locals.lookup (ofString "mode") ∧
    post.memory top = s.memory top := by
  rw [source_witness_extension] at run
  obtain ⟨guardPost,guardRun,scopeRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have same := mpt_fail_guard_normal_state s guardPost _ 8 code guardRun
  subst guardPost
  rw [source_witness_extension_kind_scope] at scopeRun
  obtain ⟨kind,output,initialized,childRun,postEq⟩ := evaluate_dec_normal_scope s post
    (ofString "ck") .one _ _ scopeRun
  let entered := setVarHOLFinite (ofString "ck") kind s
  obtain ⟨guardPost,guardRun,constructorRun⟩ := witness_extension_sequence_normal_parts entered output _ _ childRun
  have same := mpt_fail_guard_normal_state entered guardPost _ 8 code guardRun
  subst guardPost
  have atTopEntered : entered.locals.lookup (ofString "top") = some (.val (.word top)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ck" ≠ ofString "top" by decide] using atTop
  have atResultEntered : entered.locals.lookup (ofString "result") = some (.val (.word child)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ck" ≠ ofString "result" by decide] using atResult
  obtain ⟨nib,length,args⟩ := witness_extension_constructor_normal_arguments entered output child atResultEntered constructorRun
  have facts := witness_extension_constructor_normal_progress entered output top heap prev nib length child
    atTopEntered args prevCell atHeap before heapBound code constructorRun
  rw [postEq]
  refine ⟨?_,?_,?_,facts.2.2.2⟩
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact facts.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact facts.2.1
  · change (HolFiniteMapExact.resVarEq output.locals _).lookup _ = _
    rw [restore_other_local _ _ _ _ (by decide),facts.2.2.1]
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ck" ≠ ofString "mode" by decide]

#print axioms witness_extension_constructor_normal_arguments
#print axioms witness_extension_normal_progress

#print axioms witness_extension_constructor_normal_progress
end InitECandidate.Runtime
