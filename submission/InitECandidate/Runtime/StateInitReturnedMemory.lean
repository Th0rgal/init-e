import InitECandidate.Runtime.StateInitWitnessCallReturnedMemory
import InitECandidate.Runtime.StateInitUniformBound
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem state_init_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length oldWs root codes emptyRoot : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout (stateInitDbContext s layout.table) scratch heap pointer length)
 (atTable : s.locals.lookup (ofString "nodedb")=some (.val (.word layout.table)))
 (atRoot : s.locals.lookup (ofString "state_root")=some (.val (.word root)))
 (atCodes : s.locals.lookup (ofString "codedb")=some (.val (.word codes)))
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (value : ValueHOL 64) (budget : stateInitSourceCeiling≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_state_init)=(some (.returned value),post)) : ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 have code : s.code=originalRuntimeCode := valid.code
 have atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := valid.atHeap
 by_cases room : heap.toNat+40≤33806089496
 · obtain ⟨ready,prefixRun,readyClock,locals,installed,addrs,endian,ws,heapPost,_,_,_,frame,globals⟩ :=
    evaluate_state_init_world_prefix_exact_room s heap oldWs layout.table root codes
     (stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init)) code
     (by unfold stateInitSourceCeiling at budget;omega) atHeap atWs atTable atRoot atCodes room domain
   have rounded := allocationEnd_covers heap 40 (by change heap.toNat+40≤33806089496;exact room)
   have request : (40#64)≤(33806089496#64)-heap := by
    apply BitVec.le_def.mpr
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr valid.heapBound)]
    change 40≤33806089496-heap.toNat;omega
   have newValid := valid.after_heap_frame layout (stateInitDbContext s layout.table)
    (stateInitDbContext ready layout.table) scratch heap (allocationEnd heap 40) pointer length addrs endian installed frame
    (by simp [stateInitDbContext,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [show (stateInitDbContext ready layout.table).globals=ready.globals from rfl,
       globals _ (by decide) (by decide)];exact valid.atScratch)
    (by rw [show (stateInitDbContext ready layout.table).globals=ready.globals from rfl,
       globals _ (by decide) (by decide)];exact valid.atFrame)
    heapPost (by have covers:=rounded.1;change heap.toNat+40≤_ at covers;omega) rounded.2.2
    (allocationEnd_within_heap heap 40 valid.heapBound request)
   have actual : evaluateHOLFiniteState ready (stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post) := by
    rw [source_state_init_world_prefix,prefixRun] at run
    exact run
   have memory:=state_init_witness_call_returned_memory layout ready post scratch (allocationEnd heap 40) pointer length root emptyRoot heap
    newValid (by rw [locals];exact atTable) (by rw [locals];exact atRoot)
    (by rw [globals _ (by decide) (by decide)];exact atEmpty) ws
    (by have a:=valid.dbHeapBeforeFloor;have b:=valid.floorBeforeHeap;omega) room
    (by intro address hi;rw [addrs];exact domain address hi) value
    (by rw [readyClock];unfold stateInitSourceCeiling at budget;omega) actual
   intro watched lo hi
   rw [memory watched lo hi]
   exact frame watched (by have a:=valid.dbHeapBeforeFloor;have b:=valid.floorBeforeHeap;omega)
 · have rejected : ((33806089496#64)-heap).toNat<(40#64).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr valid.heapBound)]
    change 33806089496-heap.toNat<40;omega
   have failure := state_init_world_allocation_failure s (.const 40) heap 40
    (by rw [evalListHOLFinite_eq_toExact];rfl) code atHeap rejected
    (by unfold stateInitSourceCeiling at budget;omega)
   rw [source_state_init_world_prefix] at run
   unfold stateInitWorldPrefix at run
   have control := evaluate_handlerFree_call_control s (some (.global,ofString "ws")) (ofString "alloc") [.const 40]
   obtain ⟨next,normal,_⟩ := seq_returned_of_nonreturning_first (fun v=>control.2.2 v) run
   exact False.elim (failure.1 (by rw [normal]))
#print axioms state_init_returned_memory
end InitECandidate.Runtime
