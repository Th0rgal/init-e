import InitECandidate.Runtime.RollbackAllocationCopySeparation
import InitECandidate.Runtime.RollbackWorldMemcpyValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual saved-key allocation and copy reach any continuation in the same
separated world. Copy separation follows from allocation, not an extra premise. -/
theorem RollbackWorld.allocate_copy_key_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (targets watchedTables : Set (BitVec 64)) (watched : watchedTables ⊆ tables)
    (registered : ∀ table ∈ watchedTables, HashTableValuesIn table targets state)
    (witness : BitVec 64) (member : witness ∈ tables)
    (pointer source size : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word source)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 2 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer size).toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")]
        (.seq (.call (some (none,none)) (ofString "memcpy")
          [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")]) continuation)) =
      (let output := evaluateHOLFiniteState post continuation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "kc",state.locals.lookup (ofString "kc"))}))) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post ∧
      (∀ table ∈ watchedTables, HashTableValuesIn table targets post) ∧
      state.clock ≤ post.clock + size.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "kc") (.val (.word pointer)) state).locals ∧
      post.memaddrs = state.memaddrs ∧ post.code = state.code ∧ post.be = state.be ∧ HeapGlobalsFrame state post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) := by
  have allocArgs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.var .local (ofString "klen")] = some [.val (.word size)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,sizeLocal]
  obtain ⟨allocated,decl,midWorld,midSep,kc,clock,memory,midCode,domain,endian,globals,heapNext,locals⟩ :=
    world.allocate_key separated (.var .local (ofString "klen")) pointer size allocArgs code (by omega) heap pointerBound request finish
  have key : allocated.locals.lookup (ofString "key") = some (.val (.word source)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "key" from by decide] using keyLocal
  have klen : allocated.locals.lookup (ofString "klen") = some (.val (.word size)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "kc" ≠ ofString "klen" from by decide] using sizeLocal
  have copyArgs : evalListHOLFinite allocated (h := fun address => Classical.propDecidable (allocated.memaddrs address))
      [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")] = some [.val (.word pointer),.val (.word source),.val (.word size)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,kc,key,klen]
  obtain ⟨post,copy,postWorld,postSep,postRegistered,cost,remaining,postGlobals,postCode,postDomain,postEndian,postLocals⟩ :=
    midWorld.memcpy_preserves_values_in allocated widths tables witness member journal snapshot count midSep targets watchedTables watched
      (by intro table belongs; exact (registered table belongs).after_read memory domain endian)
      (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen")) pointer source size
      (allocationGuard_sum_bound pointer size pointerBound request) aligned sourceAligned (by omega)
      (by simpa only [domain] using wordDomain) (by simpa only [domain] using byteDomain)
      (by simpa only [domain] using sourceWords) (by simpa only [domain] using sourceBytes)
      (world.copy_separation_after_memory pointer heap memory) copyArgs (world.journal_before_frontier pointer witness member heap)
  refine ⟨post,?_,postWorld,postSep,postRegistered,by omega,by omega,postLocals.trans locals,postDomain.trans domain,postCode.trans midCode,postEndian.trans endian,
    globals.trans (HeapGlobalsFrame.of_globals postGlobals),by rw [postGlobals]; exact heapNext⟩
  intro continuation
  rw [decl]
  have seqRun : evaluateHOLFiniteState allocated (.seq (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")]) continuation) = evaluateHOLFiniteState post continuation := by
    rw [evaluateHOLFiniteState_seq_line780,copy]
  rw [seqRun]

#print axioms RollbackWorld.allocate_copy_key_values_in
end InitECandidate.Runtime
