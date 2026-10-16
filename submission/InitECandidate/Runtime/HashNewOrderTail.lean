import InitECandidate.Runtime.HashNewFinalAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_htabNew_order_tail : htabNewAfterZero =
    .decCall (ofString "order") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "cap"),.const 8]]
      (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "order")))
        htabNewFinalAllocation) := by rfl

/-- The two final original constructor allocations return the table in two
source clocks and preserve every occupancy array separated from the header. -/
theorem evaluate_htabNew_order_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64)) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterZero = (some (.returned (.val (.word table))),post) ∧
      post.clock = state.clock - 2 ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ used slots : BitVec 64,
        (∀ index : BitVec 64, index.toNat < slots.toNat →
          panByteAlignHOL (used + index) ≠ table + 56 ∧ panByteAlignHOL (used + index) ≠ table + 64) →
        hashOccupiedCount slots (hashOccupancyRead post used) = hashOccupiedCount slots (hashOccupancyRead state used) := by
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
  obtain ⟨last,tail,lastTicks,_,lastCode,lastAddresses,lastEndian,_,counts⟩ :=
    evaluate_htabNew_final_allocation ready (allocationEnd pointer (capacity * 8)) table capacity
      (postCode.trans code) (by omega) heap nextGuard nextFinish t c (by rw [addresses]; exact domain64)
  rw [source_htabNew_order_tail,run]
  rw [tail]
  refine ⟨_,rfl,by change last.clock = state.clock - 2; omega,
    lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,?_⟩
  intro used slots separate
  change hashOccupiedCount slots (hashOccupancyRead last used) = _
  rw [counts used slots (fun index inside => (separate index inside).2)]
  have first := sourceWriteWord_occupancy_preserved state slots used (table + 56) pointer
    (fun index inside => (separate index inside).1)
  apply Eq.trans _ first
  apply hashOccupiedCount_congr
  intro index _
  unfold hashOccupancyRead
  rw [memory,addresses,endian]
  rfl

#print axioms source_htabNew_order_tail
#print axioms evaluate_htabNew_order_tail
end InitECandidate.Runtime
