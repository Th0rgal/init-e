import InitECandidate.Runtime.RunAttemptInitializerFacts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual header validation and selected-parent zero-cost prefix preserve the
initialized workspace/world globals and derive the parent's persistent floor. -/
theorem run_attempt_selected_witness_workspace {F : Type}
 (s selected validated : PanSemStateFiniteExact 64 F)
 (si payload array count inputLength heap keccakState keccakPad stateArray stateCount codeArray codeCount liveHeap parent root : BitVec 64)
 (facts : RunAttemptSelectedWitnessFacts s selected validated si payload array count inputLength heap keccakState keccakPad
  stateArray stateCount codeArray codeCount liveHeap parent root)
 (code : s.code=originalRuntimeCode) (heapUpper : heap.toNat≤33805910000)
 (inputBefore : 2713731432+inputLength.toNat≤heap.toNat) :
 heap.toNat≤liveHeap.toNat ∧ liveHeap.toNat≤33806089496 ∧ 2713731432≤parent.toNat ∧
 selected.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))) ∧
 selected.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))) ∧
 selected.globals.lookup (ofString "keccak_st")=some (.val (.word keccakState)) ∧
 selected.globals.lookup (ofString "keccak_pad")=some (.val (.word keccakPad)) ∧
 (∀key,key∈headersInitializerGlobals→selected.globals.lookup key=s.globals.lookup key) := by
 obtain ⟨headerFacts,_,finalEq,_,heapPtr,_,_,_,parentFloor,rest⟩ := facts
 have originalFacts:=headerFacts
 obtain ⟨value,bodyPost,run,locals,readyMemory,readyGlobals,readyDomain,readyCode,valueShape,
  atVh,countBound,frontier,scratchPost,framePost,statePost,padPost,rest⟩:=headerFacts
 obtain ⟨frontierHeap,frontierAt,growth,capped,_,_,_⟩:=frontier
 have selectedGlobal (key : MlS) (notCount : ofString "block_hashes_n"≠key)
  (notHashes : ofString "block_hashes"≠key) : selected.globals.lookup key=validated.globals.lookup key := by
  rw [finalEq]
  simp [setGlobalHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notCount,notHashes]
 have frontierEq : liveHeap=frontierHeap := by
  have same := heapPtr.symm.trans ((selectedGlobal (ofString "heap_ptr") (by decide) (by decide)).trans frontierAt)
  exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj same))
 subst frontierHeap
 have size := (validate_headers_allocation_sizes count countBound).1
 have allocated := allocationEnd_covers heap (validateHeadersHsSize count) (by rw [size];omega)
 have before := allocated.1
 have parentAbove : 2713731432≤parent.toNat := by omega
 refine ⟨growth,capped,parentAbove,?_,?_,?_,?_,?_⟩
 · rw [selectedGlobal _ (by decide) (by decide)];exact scratchPost
 · rw [selectedGlobal _ (by decide) (by decide)];exact framePost
 · rw [selectedGlobal _ (by decide) (by decide)];exact statePost
 · rw [selectedGlobal _ (by decide) (by decide)];exact padPost
 · intro key member
   have notCount : ofString "block_hashes_n"≠key := by
    intro equal;rw [←equal] at member;simp (config:={decide:=true}) [headersInitializerGlobals] at member
   have notHashes : ofString "block_hashes"≠key := by
    intro equal;rw [←equal] at member;simp (config:={decide:=true}) [headersInitializerGlobals] at member
   rw [selectedGlobal key notCount notHashes]
   exact originalFacts.initializer_global _ _ si array count 2713731432 inputLength 2713714688 2701135872 heap
    keccakState keccakPad 2713731432 code key member
#print axioms run_attempt_selected_witness_workspace
end InitECandidate.Runtime
