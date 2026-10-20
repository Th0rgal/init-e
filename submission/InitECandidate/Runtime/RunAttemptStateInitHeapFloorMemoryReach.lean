import InitECandidate.Runtime.RunAttemptStateInitDiscardMemory
import InitECandidate.Runtime.RunAttemptStateInitArguments
import InitECandidate.Runtime.RunAttemptStateInitDiscardHeapFloor
import InitECandidate.Runtime.StateInitCallerDatabaseBound
import InitECandidate.Runtime.HandlerFreeDiscardReaches
import InitECandidate.Runtime.PanDiscardNormalBody
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
theorem run_attempt_state_init_heap_floor_memory_reaches {F : Type}
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
 (args : evalListHOLFinite final (h:=fun address=>Classical.propDecidable (final.memaddrs address)) runAttemptStateInitArguments=
  some [.val (.word heap),.val (.word root),.val (.word midHeap)])
 (lookup : lookupCodeHOLFinite final.code.lookup (ofString "state_init")
  [.val (.word heap),.val (.word root),.val (.word midHeap)]=
  some (sourceFunctionBody Guest.guestFn_state_init,stateInitCallee heap root midHeap,.one))
 (budget : stateInitSourceCeiling+1≤final.clock)
 : Reaches final (runAttemptAt 11) (fun post=>StateInitHeapFloorReady finalHeap.toNat post ∧post.locals=final.locals ∧
  post.code=final.code ∧post.memaddrs=final.memaddrs ∧
  (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<finalHeap.toNat→post.memory watched=final.memory watched)) (stateInitSourceCeiling+1) (runAttemptAt 12) := by
 have bodyBound:=runBounded_state_init_from_database_frame s final si heap array count inputLength statePad pad output midHeap finalHeap
  root oldWs emptyRoot linked inputSmall inputEnd code installed domain fullDomain heapPost growth aligned capped built entries arrayAbove
  stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty budget
 have callBound:=runBounded_discard_of_body final (ofString "state_init") runAttemptStateInitArguments _ _ _ _ stateInitSourceCeiling
  args lookup bodyBound budget
 rw [source_run_attempt_state_init_call]
 apply reaches_seq_of_runBounded final _ _ _ _ callBound
  (evaluate_handlerFree_call_control final none (ofString "state_init") runAttemptStateInitArguments).2.2
 intro post run
 have heapReady:=run_attempt_state_init_discard_normal_heap_floor s final post si heap array count inputLength statePad pad output
  midHeap finalHeap root oldWs emptyRoot linked inputSmall inputEnd code installed domain fullDomain heapPost growth aligned capped
  built entries arrayAbove stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty args lookup budget run
 have memory:=run_attempt_state_init_discard_normal_memory s final post si heap array count inputLength statePad pad output
  midHeap finalHeap root oldWs emptyRoot linked inputSmall inputEnd code installed domain fullDomain heapPost growth aligned capped
  built entries arrayAbove stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty args lookup budget run
 have metadata:=evaluateHOLFiniteState_metadata final (.call (some (none,none)) (ofString "state_init") runAttemptStateInitArguments)
 rw [run] at metadata
 exact ⟨heapReady.1,heapReady.2,metadata.1,metadata.2.1,memory.1⟩
#print axioms run_attempt_state_init_heap_floor_memory_reaches
end InitECandidate.Runtime
