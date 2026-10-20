import InitECandidate.Runtime.StateInitWitnessCallBound
import InitECandidate.Runtime.StateInitWorldPrefixExactRoom
import InitECandidate.Runtime.StateInitWorldAllocationFailure
import InitECandidate.Runtime.WitnessTraversalEntryAfterHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Fixed all-outcome source-step ceiling for original state_init. -/
def stateInitSourceCeiling : Nat := 2+(decodeWitnessToMptSourceCeiling+399)

/-- Complete original state_init bound from concrete original witness/database
layout and typed actual arguments. Its actual WS40 allocation is split at its
exact guard; neither success nor additional heap reserve is assumed. -/
theorem runBounded_state_init_uniform {F : Type} (layout : WitnessTraversalLayout)
 (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length oldWs root codes emptyRoot : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout (stateInitDbContext s layout.table) scratch heap pointer length)
 (atTable : s.locals.lookup (ofString "nodedb")=some (.val (.word layout.table)))
 (atRoot : s.locals.lookup (ofString "state_root")=some (.val (.word root)))
 (atCodes : s.locals.lookup (ofString "codedb")=some (.val (.word codes)))
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (budget : stateInitSourceCeiling≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_state_init) stateInitSourceCeiling := by
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
   have readyBound := runBounded_state_init_witness_call layout ready scratch (allocationEnd heap 40) pointer length root emptyRoot
    newValid (by rw [locals];exact atTable) (by rw [locals];exact atRoot)
    (by rw [globals _ (by decide) (by decide)];exact atEmpty)
    (by rw [readyClock];unfold stateInitSourceCeiling at budget;omega)
   unfold RunBounded at readyBound ⊢
   rw [source_state_init_world_prefix,prefixRun]
   unfold stateInitSourceCeiling
   exact ⟨by rw [readyClock] at readyBound;omega,by have h:=readyBound.2.1;rw [readyClock] at h;omega,readyBound.2.2⟩
 · have rejected : ((33806089496#64)-heap).toNat<(40#64).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr valid.heapBound)]
    change 33806089496-heap.toNat<40;omega
   have failure := state_init_world_allocation_failure s (.const 40) heap 40
    (by rw [evalListHOLFinite_eq_toExact];rfl) code atHeap rejected
    (by unfold stateInitSourceCeiling at budget;omega)
   rw [source_state_init_world_prefix]
   unfold stateInitWorldPrefix stateInitSourceCeiling
   apply RunBounded.seq (a:=2) (b:=decodeWitnessToMptSourceCeiling+399)
    (RunBounded.ofProg (ProgBounded.alloc _ _) code (by unfold stateInitSourceCeiling at budget;omega)) budget
   intro ready normal _ _
   exact False.elim (failure.1 (by rw [normal]))
#print axioms runBounded_state_init_uniform
end InitECandidate.Runtime
