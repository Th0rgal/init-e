import InitECandidate.Runtime.RunAttemptSelectedWitnessWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Complete actual entry/header/selected-root/two-database composition up to
state_init. Every original header and database fact is retained at the actual
intermediate states; the initializer callee bound is derived, never assumed. -/
theorem run_attempt_entry_initialized_state_init_reaches {F : Type}
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
 (budget : runAttemptEntryInitializerCost≤s.clock) :
 Reaches s (runAttemptAt 0)
  (fun final=>∃selected validated : PanSemStateFiniteExact 64 F, ∃liveHeap parent root : BitVec 64,
   RunAttemptSelectedWitnessFacts s selected validated si payload array count inputLength heap keccakState keccakPad
    stateArray stateCount codeArray codeCount liveHeap parent root ∧
   RunAttemptInitializedWitnessFacts selected final liveHeap stateCount stateArray codeCount codeArray
    keccakState keccakPad output parent root)
  runAttemptEntryInitializerCost (runAttemptAt 11) := by
 have first := run_attempt_entry_all_witness_selected_root_reaches s si payload array count (2713731432#64)
  inputLength (2713714688#64) (2701135872#64) heap keccakState keccakPad stateArray stateCount codeArray codeCount
  2713731432 134217712 (fullDomain _ (by simp only [BitVec.add_zero];omega)) siCell inputSmall (Nat.le_refl _)
  (Nat.le_refl _) tableAbove inputBefore (by decide) (by decide) (by decide) (by decide) stateBelow padBelow
  atSi linked stateLinked stateArrayAbove codeLinked codeArrayAbove scratchGlobal frameGlobal stateGlobal padGlobal
  (by intro address lo hi;exact fullDomain address (by omega))
  (by intro address lo hi;exact fullDomain address hi) heapGlobal heapUpper (by omega) code recordAbove recordBefore
  (by unfold runAttemptEntryInitializerCost at budget;omega)
 change Reaches s (runAttemptAt 0)
  (fun selected=>∃validated : PanSemStateFiniteExact 64 F, ∃liveHeap parent root : BitVec 64,
   RunAttemptSelectedWitnessFacts s selected validated si payload array count inputLength heap keccakState keccakPad
    stateArray stateCount codeArray codeCount liveHeap parent root)
  (validateHeadersBodyCost 134217712+1) (runAttemptAt 9) at first
 apply reaches_trans_budget s (runAttemptAt 0) (runAttemptAt 9) (runAttemptAt 11) _ _
  (validateHeadersBodyCost 134217712+1) (2*nodedbInputCallCost 134217712) budget first
 intro selected selectedFacts ticks
 obtain ⟨validated,liveHeap,parent,root,facts⟩:=selectedFacts
 have retained:=facts
 obtain ⟨headerFacts,nonzero,finalEq,atParent,heapPost,rootWord,rootDomain,parentBefore,parentFloor,
  stateLinkedPost,codeLinkedPost,siPost,codePost,domainPost,alignedPost⟩:=facts
 obtain ⟨growth,capped,parentAbove,scratchPost,framePost,statePost,padPost,keptGlobals⟩:=
  run_attempt_selected_witness_workspace s selected validated si payload array count inputLength heap keccakState keccakPad
   stateArray stateCount codeArray codeCount liveHeap parent root retained code heapUpper inputBefore
 have outputPost : selected.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word output)) := by
  rw [keptGlobals _ (by simp [headersInitializerGlobals])];exact outputGlobal
 have wsPost : selected.globals.lookup (ofString "ws")=some (.val (.word oldWs)) := by
  rw [keptGlobals _ (by simp [headersInitializerGlobals])];exact wsGlobal
 have emptyPost : selected.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)) := by
  rw [keptGlobals _ (by simp [headersInitializerGlobals])];exact emptyGlobal
 have stateCost := nodedb_call_cost_le_input stateCount inputLength 134217712 stateLinkedPost.countBound inputSmall (Nat.le_refl _)
 have codeCost := nodedb_call_cost_le_input codeCount inputLength 134217712 codeLinkedPost.countBound inputSmall (Nat.le_refl _)
 have dbCost : (nodedbBodyCost stateCount+1)+(nodedbBodyCost codeCount+1)≤2*nodedbInputCallCost 134217712 := by omega
 have stateWindows (nonzero : stateCount≠0) : keccakState.toNat+200≤stateArray.toNat ∧
  keccakPad.toNat+136≤stateArray.toNat ∧ output.toNat+32≤stateArray.toNat := by
  have above : 2713731432≤stateArray.toNat := by
   rcases stateArrayAbove with zero|above
   · exact False.elim (nonzero (BitVec.eq_of_toNat_eq (by simpa using zero)))
   · exact above
  exact ⟨by omega,by omega,by omega⟩
 have codeWindows (nonzero : codeCount≠0) : keccakState.toNat+200≤codeArray.toNat ∧
  keccakPad.toNat+136≤codeArray.toNat ∧ output.toNat+32≤codeArray.toNat := by
  have above : 2713731432≤codeArray.toNat := by
   rcases codeArrayAbove with zero|above
   · exact False.elim (nonzero (BitVec.eq_of_toNat_eq (by simpa using zero)))
   · exact above
  exact ⟨by omega,by omega,by omega⟩
 have databaseRun := run_attempt_selected_parent_state_init_bound_reaches selected si liveHeap stateCount stateArray codeCount codeArray
  (2713731432#64) inputLength keccakState keccakPad output parent root oldWs emptyRoot 2713731432 atParent rootWord rootDomain
  parentAbove parentBefore siPost stateLinkedPost codeLinkedPost codePost heapPost alignedPost capped statePost padPost outputPost
  inputSmall outputAligned stateWindows codeWindows
  (by intro address al lo hi;rw [domainPost];exact fullDomain address hi)
  (by omega) stateBelow padBelow outputBelow recordAbove (by omega) stateArrayAbove codeArrayAbove rfl rfl
  (by change 2713731432+inputLength.toNat≤liveHeap.toNat;omega) (by intro address hi;rw [domainPost];exact fullDomain address hi) scratchPost framePost wsPost emptyPost
 change Reaches selected (runAttemptAt 9)
  (fun final=>RunAttemptInitializedWitnessFacts selected final liveHeap stateCount stateArray codeCount codeArray
    keccakState keccakPad output parent root)
  ((nodedbBodyCost stateCount+1)+(nodedbBodyCost codeCount+1)) (runAttemptAt 11) at databaseRun
 apply reaches_mono selected (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ dbCost _ databaseRun
 intro final databaseFacts
 exact ⟨selected,validated,liveHeap,parent,root,retained,databaseFacts⟩
#print axioms run_attempt_entry_initialized_state_init_reaches
end InitECandidate.Runtime
