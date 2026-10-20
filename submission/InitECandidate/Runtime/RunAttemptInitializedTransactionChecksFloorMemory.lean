import InitECandidate.Runtime.RunAttemptStateInitHeapFloorMemoryReach
import InitECandidate.Runtime.RunAttemptTransactionPresencePrefix
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual initializer and transaction-presence checks compose, with their
real callee bound and returned heap derived from the original database metadata. -/
theorem run_attempt_initialized_transaction_checks_floor_memory_reaches {F : Type}
 (s final : PanSemStateFiniteExact 64 F)
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
 (payload : BitVec 64)
 (atPayload : final.locals.lookup (ofString "pl")=some (.val (.word payload)))
 (budget : (stateInitSourceCeiling+1)+(2^64-1)≤final.clock)
 : Reaches final (runAttemptAt 11)
  (fun post=>StateInitHeapFloorReady finalHeap.toNat post ∧post.code=final.code ∧post.memaddrs=final.memaddrs ∧
   (∀key,key≠ofString "i"→key≠ofString "txs"→key≠ofString "ntx"→post.locals.lookup key=final.locals.lookup key) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<finalHeap.toNat→post.memory watched=final.memory watched))
  ((stateInitSourceCeiling+1)+(2^64-1)) (runAttemptAt 17) := by
 let resultFacts := fun post : PanSemStateFiniteExact 64 F =>
  StateInitHeapFloorReady finalHeap.toNat post ∧post.code=final.code ∧post.memaddrs=final.memaddrs ∧
   (∀key,key≠ofString "i"→key≠ofString "txs"→key≠ofString "ntx"→post.locals.lookup key=final.locals.lookup key) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<finalHeap.toNat→post.memory watched=final.memory watched)
 change Reaches final (runAttemptAt 11) resultFacts ((stateInitSourceCeiling+1)+(2^64-1)) (runAttemptAt 17)
 have initialized:=run_attempt_state_init_heap_floor_memory_reaches s final final si heap array count inputLength statePad pad output
  midHeap finalHeap root oldWs emptyRoot linked inputSmall inputEnd code installed domain fullDomain heapPost growth aligned capped
  built entries arrayAbove stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty args lookup (Nat.le_trans (Nat.le_add_right _ _) budget)
 apply reaches_trans_budget final (runAttemptAt 11) (runAttemptAt 12) (runAttemptAt 17) _ resultFacts
  (stateInitSourceCeiling+1) (2^64-1) budget initialized
 intro ready facts ticks
 obtain ⟨readyHeap,readyLocals,readyCode,readyDomain,readyMemory⟩:=facts
 have readyPayload : ready.locals.lookup (ofString "pl")=some (.val (.word payload)) := by
  rw [readyLocals];exact atPayload
 have presence:=run_attempt_tx_presence_prefix ready payload (readyCode.trans (installed.trans code)) readyPayload ticks
 have strengthened:=reaches_mono ready (runAttemptAt 13) (runAttemptAt 17) _ resultFacts _ _ (Nat.le_refl _) (by
  intro post facts
  obtain ⟨memory,domainPost,codePost,endian,globalsPost,localsPost⟩:=facts
  refine ⟨?_,codePost.trans readyCode,domainPost.trans readyDomain,?_,?_⟩
  · obtain ⟨pointer,atPointer,alignedPost,cappedPost,floorPost⟩:=readyHeap
    exact ⟨pointer,(globalsPost _).trans atPointer,alignedPost,cappedPost,floorPost⟩
  · intro key notIndex notArray notCount
    rw [localsPost key notIndex notArray notCount,readyLocals]
  · intro watched lo hi
    exact (congrFun memory watched).trans (readyMemory watched lo hi)) presence
 have skip : Reaches ready (runAttemptAt 12) (fun next=>next=ready) 0 (runAttemptAt 13) := by
  rw [show runAttemptAt 12=.seq .skip (runAttemptAt 13) from rfl]
  apply reaches_seq
  exact Or.inl ⟨ready,rfl,by simp,le_refl _,evaluateHOLFiniteState_skip ready⟩
 have composed:=reaches_trans ready (runAttemptAt 12) (runAttemptAt 13) (runAttemptAt 17) _ resultFacts 0 (2^64-1)
  skip (by intro next eq;subst next;exact strengthened)
 simpa only [Nat.zero_add] using composed
#print axioms run_attempt_initialized_transaction_checks_floor_memory_reaches
end InitECandidate.Runtime
