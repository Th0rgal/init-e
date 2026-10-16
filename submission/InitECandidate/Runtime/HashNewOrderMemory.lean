import InitECandidate.Runtime.HashNewOrderTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact memory effect of the original constructor's last two allocations. -/
theorem evaluate_htabNew_order_tail_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64)) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterZero = (some (.returned (.val (.word table))),post) ∧
      post.clock = state.clock - 2 ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.memory = (sourceWriteWord (sourceWriteWord state (table + 56) pointer)
        (table + 64) (allocationEnd pointer (capacity * 8))).memory := by
  obtain ⟨guard,finish,nextGuard,nextFinish,_⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,ticks,locals,memory,_,heap,postCode,addresses,endian⟩ :=
    evaluate_allocation_pointer_store state (ofString "order") (ofString "t") _ pointer (capacity * 8)
      table 56 htabNewFinalAllocation (by decide) arguments code (by omega) heapGlobal guard finish tableLocal domain56
  have nt : ofString "order" ≠ ofString "t" := by decide
  have nc : ofString "order" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨last,tail,lastTicks,_,lastCode,lastAddresses,lastEndian,lastMemory,counts⟩ :=
    evaluate_htabNew_final_allocation ready (allocationEnd pointer (capacity * 8)) table capacity
      (postCode.trans code) (by omega) heap nextGuard nextFinish t c (by rw [addresses]; exact domain64)
  rw [source_htabNew_order_tail,run]
  rw [tail]
  refine ⟨_,rfl,by change last.clock = state.clock - 2; omega,
    lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
  funext address
  change last.memory address = _
  rw [lastMemory]
  simp only [sourceWriteWord]
  rw [memory]
  rfl

/-- The final pointer writes retain every earlier constructor header field. -/
theorem htabNew_order_memory_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer capacity : BitVec 64) :
    let post := sourceWriteWord (sourceWriteWord state (table + 56) pointer)
      (table + 64) (allocationEnd pointer (capacity * 8))
    post.memory (table + 56) = .word pointer ∧
      post.memory (table + 64) = .word (allocationEnd pointer (capacity * 8)) ∧
      ∀ offset ∈ ([0,8,16,24,32,40,48] : List Nat),
        post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simp [sourceWriteWord]
  · simp [sourceWriteWord]
  · intro offset member
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sourceWriteWord]

#print axioms htabNew_order_memory_fields
#print axioms evaluate_htabNew_order_tail_memory
end InitECandidate.Runtime
