import InitECandidate.Runtime.HashNewOrderMemory
import InitECandidate.Runtime.HashNewFinalHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_htabNew_order_tail_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer table capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : 2 ≤ state.clock)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (safe : AllocationPlanSafe pointer [capacity * 8,capacity * 8])
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain56 : state.memaddrs (table + 56)) (domain64 : state.memaddrs (table + 64)) :
    ∃ post, evaluateHOLFiniteState state htabNewAfterZero = (some (.returned (.val (.word table))),post) ∧
      post.clock = state.clock - 2 ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd pointer (capacity * 8)) (capacity * 8)))) ∧
      HeapGlobalsFrame state post ∧
      post.memory = (sourceWriteWord (sourceWriteWord state (table + 56) pointer)
        (table + 64) (allocationEnd pointer (capacity * 8))).memory := by
  obtain ⟨guard,finish,nextGuard,nextFinish,_⟩ := safe
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.panop .mul [.var .local (ofString "cap"),.const 8]] = some [.val (.word (capacity * 8))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,run,ticks,locals,memory,_,heap,postCode,addresses,endian,globalsFrame⟩ :=
    evaluate_allocation_pointer_store_heap_frame state (ofString "order") (ofString "t") _ pointer (capacity * 8)
      table 56 htabNewFinalAllocation (by decide) arguments code (by omega) heapGlobal guard finish tableLocal domain56
  have nt : ofString "order" ≠ ofString "t" := by decide
  have nc : ofString "order" ≠ ofString "cap" := by decide
  have t : ready.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nt] using tableLocal
  have c : ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [locals]; simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc] using capLocal
  obtain ⟨last,tail,lastTicks,_,lastHeap,lastCode,lastAddresses,lastEndian,lastMemory,lastFrame,counts⟩ :=
    evaluate_htabNew_final_allocation_heap_frame ready (allocationEnd pointer (capacity * 8)) table capacity
      (postCode.trans code) (by omega) heap nextGuard nextFinish t c (by rw [addresses]; exact domain64)
  rw [source_htabNew_order_tail,run]
  rw [tail]
  refine ⟨_,rfl,by change last.clock = state.clock - 2; omega,
    lastCode.trans postCode,lastAddresses.trans addresses,lastEndian.trans endian,lastHeap,globalsFrame.trans lastFrame,?_⟩
  funext address
  change last.memory address = _
  rw [lastMemory]
  simp only [sourceWriteWord]
  rw [memory]
  rfl

#print axioms evaluate_htabNew_order_tail_heap_frame
end InitECandidate.Runtime
