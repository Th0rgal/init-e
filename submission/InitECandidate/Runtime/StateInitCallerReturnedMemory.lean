import InitECandidate.Runtime.StateInitReturnedMemory
import InitECandidate.Runtime.StateInitDatabaseLayout
import InitECandidate.Runtime.WitnessSlicesDatabaseFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Instantiate the complete original initializer at its real three-argument
callee entry using actual two-database metadata and preserved original witnesses.
No decoder-entry predicate or callee bound is a premise. -/
theorem state_init_from_database_frame_returned_memory {F : Type}
 (s final post : PanSemStateFiniteExact 64 F)
 (si heap array count inputLength statePad pad output midHeap finalHeap root oldWs emptyRoot : BitVec 64)
 (linked : WitnessArrayLinked s si 40 48 array count (2713731432#64) inputLength heap)
 (inputSmall : inputLength.toNat≤134217712)
 (inputEnd : 2713731432+inputLength.toNat≤heap.toNat)
 (code : s.code=originalRuntimeCode) (installed : final.code=s.code) (domain : final.memaddrs=s.memaddrs)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (heapPost : final.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
 (growth : heap.toNat≤finalHeap.toNat) (aligned : finalHeap.toNat%8=0) (capped : finalHeap.toNat≤33806089496)
 (built : NodedbTableAt final heap finalHeap count)
 (entries : HashTableValuesIn heap (NodedbSliceTargets array count) final)
 (arrayAbove : count.toNat=0 ∨ 2713731432≤array.toNat)
 (stateBelow : statePad.toNat+200≤2713731432) (padBelow : pad.toNat+136≤2713731432)
 (outputBelow : output.toNat+32≤2713731432)
 (frame : ∀address : BitVec 64,address.toNat<heap.toNat→¬MWin statePad 200 address→¬MWin pad 136 address→
  ¬MWin output 32 address→final.memory address=s.memory address)
 (globals : ∀key,key∈nodedbInitializerGlobals→final.globals.lookup key=s.globals.lookup key)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))))
 (atWs : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (value : ValueHOL 64) (budget : stateInitSourceCeiling+1≤final.clock)
 (run : evaluateHOLFiniteState (callEntryStateHOLFinite final (stateInitCallee heap root midHeap))
  (sourceFunctionBody Guest.guestFn_state_init)=(some (.returned value),post)) : ∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<finalHeap.toNat→post.memory watched=final.memory watched := by
 have finalDomain : ∀address : BitVec 64,address.toNat<33806089496→final.memaddrs address := by
  intro address hi;rw [domain];exact fullDomain address hi
 have scratchPost : final.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))) := by
  rw [globals _ (by simp [nodedbInitializerGlobals])];exact atScratch
 have framePost : final.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))) := by
  rw [globals _ (by simp [nodedbInitializerGlobals])];exact atFrame
 have wsPost : final.globals.lookup (ofString "ws")=some (.val (.word oldWs)) := by
  rw [globals _ (by simp [nodedbInitializerGlobals])];exact atWs
 have emptyPost : final.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by
  rw [globals _ (by simp [nodedbInitializerGlobals])];exact atEmpty
 have slices := witness_slices_after_database_frame s final si 40 48 array count 2713731432 inputLength heap
  statePad pad output 2713731432 linked arrayAbove stateBelow padBelow outputBelow domain frame
 let layout := stateInitDatabaseLayout heap finalHeap array count inputLength
 have valid := state_init_database_layout_entry final heap finalHeap array count inputLength (installed.trans code)
  scratchPost framePost heapPost aligned capped finalDomain inputSmall (by omega) (by omega) arrayAbove
  (linked.arrayEnd.trans growth) built entries slices
 let entry := callEntryStateHOLFinite final (stateInitCallee heap root midHeap)
 have entered := valid.with_locals_clock layout (stateInitDbContext final heap) 2713714688 finalHeap 2713731432 inputLength
  (stateInitDbContext entry heap).locals entry.clock (by simp [layout,stateInitDatabaseLayout,stateInitDbContext,HolFiniteMapExact.lookup_update,FUPDATE])
 change WitnessTraversalEntryPrecondition layout (stateInitDbContext entry heap) 2713714688 finalHeap 2713731432 inputLength at entered
 exact state_init_returned_memory layout entry post 2713714688 finalHeap 2713731432 inputLength oldWs root midHeap emptyRoot entered
  (by simp (config:={decide:=true}) [entry,stateInitCallee,callEntryStateHOLFinite,layout,stateInitDatabaseLayout,
   HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp (config:={decide:=true}) [entry,stateInitCallee,callEntryStateHOLFinite,
   HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,stateInitCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  wsPost emptyPost finalDomain value (by change stateInitSourceCeiling≤final.clock-1;omega) run
#print axioms state_init_from_database_frame_returned_memory
end InitECandidate.Runtime
