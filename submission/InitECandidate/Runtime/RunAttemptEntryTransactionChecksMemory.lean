import InitECandidate.Runtime.RunAttemptEntryTransactionChecks
import InitECandidate.Runtime.RunAttemptInitializedTransactionChecksMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Actual original entry through header validation, both databases, state_init
and transaction-presence checks. Every callee bound is derived from source and
decoder metadata. Unreadable records and exceptional paths terminate within the same budget. -/
theorem run_attempt_entry_transaction_checks_memory_reaches {F : Type}
 (s : PanSemStateFiniteExact 64 F)
 (si payload array count inputLength heap keccakState keccakPad stateArray stateCount codeArray codeCount output oldWs emptyRoot : BitVec 64)
 (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
 (siCell : s.memory (si+0#64)=.word payload)
 (inputSmall : inputLength.toNat≤134217712)
 (inputBefore : 2713731432+inputLength.toNat≤heap.toNat)
 (tableAbove : 2713731432≤array.toNat)
 (linked : WitnessArrayLinked s si 72 80 array count (2713731432#64) inputLength heap)
 (stateLinked : WitnessArrayLinked s si 40 48 stateArray stateCount (2713731432#64) inputLength heap)
 (stateArrayAbove : stateCount.toNat=0 ∨ 2713731432≤stateArray.toNat)
 (codeLinked : WitnessArrayLinked s si 56 64 codeArray codeCount (2713731432#64) inputLength heap)
 (codeArrayAbove : codeCount.toNat=0 ∨ 2713731432≤codeArray.toNat)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))))
 (stateGlobal : s.globals.lookup (ofString "keccak_st")=some (.val (.word keccakState)))
 (padGlobal : s.globals.lookup (ofString "keccak_pad")=some (.val (.word keccakPad)))
 (outputGlobal : s.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word output)))
 (wsGlobal : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
 (emptyGlobal : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (stateBelow : keccakState.toNat+200≤2713731432) (padBelow : keccakPad.toNat+136≤2713731432)
 (outputBelow : output.toNat+32≤2713731432) (outputAligned : output.toNat%8=0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (heapGlobal : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapUpper : heap.toNat≤33805910000) (code : s.code=originalRuntimeCode)
 (recordAbove : 2713731432≤si.toNat) (recordBefore : si.toNat+88≤heap.toNat)
 (budget : runAttemptEntryTransactionChecksCost≤s.clock) :
 Reaches s (runAttemptAt 0)
  (fun post=>StateInitHeapReady post ∧post.code=originalRuntimeCode ∧post.memaddrs=s.memaddrs ∧
   post.locals.lookup (ofString "si")=some (.val (.word si)) ∧
   post.locals.lookup (ofString "pl")=some (.val (.word payload)) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<heap.toNat→post.memory watched=s.memory watched))
  runAttemptEntryTransactionChecksCost (runAttemptAt 17) := by
 let resultFacts:=fun post : PanSemStateFiniteExact 64 F =>
  StateInitHeapReady post ∧post.code=originalRuntimeCode ∧post.memaddrs=s.memaddrs ∧
   post.locals.lookup (ofString "si")=some (.val (.word si)) ∧
   post.locals.lookup (ofString "pl")=some (.val (.word payload)) ∧
   (∀watched : BitVec 64,2713731432≤watched.toNat→watched.toNat<heap.toNat→post.memory watched=s.memory watched)
 have initial:=run_attempt_entry_initialized_state_init_reaches s si payload array count inputLength heap keccakState keccakPad
  stateArray stateCount codeArray codeCount output oldWs emptyRoot atSi siCell inputSmall inputBefore tableAbove linked stateLinked
  stateArrayAbove codeLinked codeArrayAbove scratchGlobal frameGlobal stateGlobal padGlobal outputGlobal wsGlobal emptyGlobal
  stateBelow padBelow outputBelow outputAligned fullDomain heapGlobal heapUpper code recordAbove recordBefore
  (Nat.le_trans (Nat.le_add_right _ _) budget)
 change Reaches s (runAttemptAt 0) resultFacts
  (runAttemptEntryInitializerCost+((stateInitSourceCeiling+1)+(2^64-1))) (runAttemptAt 17)
 apply reaches_trans_budget s (runAttemptAt 0) (runAttemptAt 11) (runAttemptAt 17) _ resultFacts
  runAttemptEntryInitializerCost ((stateInitSourceCeiling+1)+(2^64-1)) budget initial
 intro final facts ticks
 obtain ⟨selected,validated,liveHeap,parent,root,selectedFacts,dbFacts⟩:=facts
 have workspace:=run_attempt_selected_witness_workspace s selected validated si payload array count inputLength heap keccakState keccakPad
  stateArray stateCount codeArray codeCount liveHeap parent root selectedFacts code heapUpper inputBefore
 obtain ⟨heapGrowth,liveCapped,parentAbove,scratchPost,framePost,statePost,padPost,keptGlobals⟩:=workspace
 have oldSelected:=selectedFacts
 obtain ⟨headerFacts,nonzero,selectedEq,atParent,atLive,rootWord,rootDomain,parentBefore,parentFloor,
  stateLinkedPost,codeLinkedPost,siSelected,codeSelected,domainSelected,alignedSelected⟩:=selectedFacts
 obtain ⟨midHeap,finalHeap,locals,domainFinal,codeFinal,endian,atState,atPad,atOutput,atHeap,
  midGrowth,finalGrowth,alignedFinal,cappedFinal,stateEntries,codeEntries,stateBuilt,codeBuilt,
  arena,memory,atParentFinal,rootWordFinal,rootDomainFinal,parentBeforeFinal,args,lookup,globals,bound⟩:=dbFacts
 have atWsSelected : selected.globals.lookup (ofString "ws")=some (.val (.word oldWs)) := by
  rw [keptGlobals _ (by simp [headersInitializerGlobals])];exact wsGlobal
 have atEmptySelected : selected.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by
  rw [keptGlobals _ (by simp [headersInitializerGlobals])];exact emptyGlobal
 have plSelected : selected.locals.lookup (ofString "pl")=some (.val (.word payload)) := by
  obtain ⟨value,bodyPost,bodyRun,headerLocals,rest⟩:=headerFacts
  rw [selectedEq]
  simp (config:={decide:=true}) [setGlobalHOLFinite,setVarHOLFinite,headerLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 have plFinal : final.locals.lookup (ofString "pl")=some (.val (.word payload)) := by
  simpa (config:={decide:=true}) [locals,HolFiniteMapExact.lookup_update,FUPDATE] using plSelected
 have siFinal : final.locals.lookup (ofString "si")=some (.val (.word si)) := by
  simpa (config:={decide:=true}) [locals,HolFiniteMapExact.lookup_update,FUPDATE] using siSelected
 have checked:=run_attempt_initialized_transaction_checks_memory_reaches selected final si liveHeap stateArray stateCount inputLength
  keccakState keccakPad output midHeap finalHeap root oldWs emptyRoot stateLinkedPost inputSmall (by omega)
  codeSelected codeFinal domainFinal (by intro address hi;rw [domainSelected];exact fullDomain address hi)
  atHeap (midGrowth.trans finalGrowth) alignedFinal cappedFinal stateBuilt stateEntries stateArrayAbove stateBelow padBelow outputBelow
  memory globals scratchPost framePost atWsSelected atEmptySelected args lookup payload plFinal ticks
 apply reaches_mono final (runAttemptAt 11) (runAttemptAt 17) _ resultFacts _ _ (Nat.le_refl _) _ checked
 intro post retained
 obtain ⟨heapReady,codePost,domainPost,localsPost,postMemory⟩:=retained
 refine ⟨heapReady,codePost.trans (codeFinal.trans codeSelected),domainPost.trans (domainFinal.trans domainSelected),
  (localsPost _ (by decide) (by decide) (by decide)).trans siFinal,
  (localsPost _ (by decide) (by decide) (by decide)).trans plFinal,?_⟩
 intro watched lower upper
 have selectedMemory : selected.memory watched=s.memory watched := by
  obtain ⟨value,bodyPost,bodyRun,headerLocals,headerMemory,headerGlobals,headerDomain,headerCode,valueShape,atVh,countCap,
   frontier,scratchKept,frameKept,stateKept,padKept,headerFrame,rest⟩:=headerFacts
  rw [selectedEq]
  simpa [setGlobalHOLFinite,setVarHOLFinite] using headerFrame watched lower upper
 have databaseMemory : final.memory watched=selected.memory watched :=
  memory watched (by omega) (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
 exact (postMemory watched lower (by omega)).trans (databaseMemory.trans selectedMemory)
#print axioms run_attempt_entry_transaction_checks_memory_reaches
end InitECandidate.Runtime
