import InitECandidate.Runtime.RunAttemptStateInitArguments
import InitECandidate.Runtime.StateInitCallerReturnedMemory
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
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
theorem run_attempt_state_init_discard_normal_memory {F : Type}
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
 (run : evaluateHOLFiniteState final (.call (some (none,none)) (ofString "state_init") runAttemptStateInitArguments)=(none,post)) :
 (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<finalHeap.toNat→post.memory watched=final.memory watched) ∧post.locals=final.locals := by
 obtain ⟨value,bodyPost,bodyRun,memoryPost,localsPost⟩ := evaluate_discard_normal_body_memory final post _ _ _ _ _ _ args lookup run
 have frame := state_init_from_database_frame_returned_memory s final bodyPost si heap array count inputLength statePad pad output
  midHeap finalHeap root oldWs emptyRoot linked inputSmall inputEnd code installed domain fullDomain heapPost growth aligned capped
  built entries arrayAbove stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty value budget bodyRun
 refine ⟨?_,localsPost⟩
 intro watched lo hi
 rw [memoryPost]
 exact frame watched lo hi
#print axioms run_attempt_state_init_discard_normal_memory
end InitECandidate.Runtime
