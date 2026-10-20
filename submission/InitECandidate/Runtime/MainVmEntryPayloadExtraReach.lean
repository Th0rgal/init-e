import InitECandidate.Runtime.MainStatelessCallNormalResult
import InitECandidate.Runtime.MainInitialHashReachOutputMetadata
import InitECandidate.Runtime.MainDecoderInitializedGlobals
import InitECandidate.Runtime.MainDecoderCallHeapUpper
import InitECandidate.Runtime.MainDecoderVmEntryReach
import InitECandidate.Runtime.MainDecoderCallOuterWitnessArrays
import InitECandidate.Runtime.WitnessArrayMemoryFrame
import InitECandidate.Runtime.WitnessSpanGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual decoder and initial hash export the payload extra-data length
cell and its input bound, together with the original decoded state/code witness
arrays to main's VM-validation continuation, with input-size bounds, and the
decoded payload cell (with its domain) still intact at the reached state. -/
theorem main_vm_entry_payload_extra_reach {F : Type} (state ready decodedState : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,decodedState))
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ decodedState.clock) :
    ∃ out si rootHeap payload array count codes codeCount headers headerCount length : BitVec 64,
      rootHeap.toNat≤5000000000 ∧ (allocationEnd rootHeap 32).toNat≤5000000040 ∧
      length.toNat≤134217712 ∧ 2713731432+length.toNat≤si.toNat ∧ si.toNat+88≤rootHeap.toNat ∧
      (count = 0 ∨ si.toNat + 88 ≤ array.toNat) ∧
      (codeCount = 0 ∨ si.toNat + 88 ≤ codes.toNat) ∧
      (headerCount = 0 ∨ si.toNat + 88 ≤ headers.toNat) ∧
      2713715344 ≤ si.toNat ∧
      Reaches decodedState (mainAt 21)
        (fun post =>
          WitnessArrayLinked post si 40 48 array count 2713731432 length (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked post si 56 64 codes codeCount 2713731432 length (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked post si 72 80 headers headerCount 2713731432 length (allocationEnd rootHeap 32) ∧
          post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
          post.locals.lookup (ofString "root") = some (.val (.word rootHeap)) ∧
          post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd rootHeap 32))) ∧
          (∀ key, key≠ofString "heap_ptr"→post.globals.lookup key=(allInitializerGlobals state.globals).lookup key) ∧
          post.memaddrs = decodedState.memaddrs ∧ post.code = originalRuntimeCode ∧
          post.memaddrs (si + (0#64)) ∧ post.memory (si + (0#64)) = .word payload ∧
          post.locals.lookup (ofString "out")=some (.val (.word out)) ∧
          (∃ extraLength : BitVec 64,extraLength.toNat≤134217712 ∧
            post.memaddrs (payload+24#64) ∧post.memory (payload+24#64)=.word extraLength) ∧
          2713731432≤payload.toNat ∧payload.toNat+136≤(allocationEnd rootHeap 32).toNat)
        (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  obtain ⟨entryLength,out,_,_,atInp,atOut,_,_,_,_,_,_,_,_,readyCode,_,_,_⟩ := valid.fields
  have decodedOut : decodedState.locals.lookup (ofString "out")=some (.val (.word out)) := by
    obtain ⟨value,bodyPost,bodyRun,shape,postEq⟩ := main_stateless_call_normal_result ready decodedState 2713731432 entryLength atInp (readyCode.trans code) run
    rw [postEq]
    simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atOut
  obtain ⟨length,si,array,count,codes,codeCount,headers,headerCount,witnessHeap,
    small,inp,inputBefore,initialBefore,wlocals,stateLinked,codesLinked,headersLinked,origin,codesOrigin,
    witnessBinding,_,_,_,recordExtent,readyHeap,headersOrigin⟩ :=
    main_decoder_call_outer_witness_arrays state ready decodedState code arena valid run
  obtain ⟨rootHeap,heap,payload,blobs,blobCount,parentRoot,record,payloadArray,payloadCount,input,inputLength,
    withdrawals,withdrawalCount,requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,
    recordAfter,decoded,finalBinding,_,cap,alignment,payloadExtent,arrayExtent,atSi,payloadOrigin,lower,workspace⟩ :=
    main_decoder_call_hash_workspace state ready decodedState code arena valid run
  obtain ⟨_,_,upperHeap,_,_,_,_,upperBinding,_,_,rootUpper,_⟩ :=
    main_decoder_call_heap_upper state ready decodedState code arena valid run
  have upperEq : upperHeap=rootHeap := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using upperBinding.symm.trans finalBinding
  subst upperHeap
  have allocationUpper : (allocationEnd rootHeap 32).toNat≤5000000040 := by
    have padded := (allocationEnd_covers rootHeap 32 (by change rootHeap.toNat+32≤33806089496; omega)).2.1
    change (allocationEnd rootHeap 32).toNat<rootHeap.toNat+32+8 at padded
    omega
  have initialized := main_decoder_call_initialized_nonheap state ready decodedState code arena valid run
  have heapEq : heap = si := by
    have siLookup : decodedState.locals.lookup (ofString "si") = some (.val (.word si)) := by
      rw [wlocals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    exact lookup_word_eq decodedState _ _ _ atSi siLookup
  subst si
  have rootEq : rootHeap = witnessHeap := by
    rw [witnessBinding] at finalBinding
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj finalBinding.symm))
  subst witnessHeap
  have reach := main_root_initial_hash_reaches_output_metadata decodedState rootHeap heap payload blobs blobCount parentRoot record
    payloadArray payloadCount input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength
    workspace atSi header table decoded lower growth recordAfter payloadExtent arrayExtent payloadOrigin budget
  refine ⟨out,heap,rootHeap,payload,array,count,codes,codeCount,headers,headerCount,length,
    rootUpper,allocationUpper,small,initialBefore,(by omega),origin,codesOrigin,headersOrigin,lower,?_⟩
  apply reaches_mono decodedState (mainAt 21) (mainAt 23) _ _ _ _ (le_refl _) ?_ reach
  intro post facts
  obtain ⟨_,_,payloadKept,siKept,rootKept,globals,domain,installed,memory,outKept⟩ := facts
  have heapGrowth : rootHeap.toNat ≤ (allocationEnd rootHeap 32).toNat := by
    rw [allocationEnd_eq_align,panByteAlign_toNat64]
    have add : (rootHeap + (32#64)).toNat = rootHeap.toNat + 32 := by
      rw [BitVec.toNat_add_of_lt (by change rootHeap.toNat + 32 < 2^64; omega)]; rfl
    have pad : ((rootHeap + (32#64)) + (7#64)).toNat = rootHeap.toNat + 32 + 7 := by
      rw [BitVec.toNat_add_of_lt (by rw [add]; change rootHeap.toNat + 32 + 7 < 2^64; omega),add]; rfl
    change rootHeap.toNat ≤ ((rootHeap + (32#64)) + (7#64)).toNat / 8 * 8
    rw [pad]
    omega
  refine ⟨stateLinked.after_memory_between_cells decodedState post _ _ _ _ _ _ _ _ _ 2713715344
      ?_ ?_ (by rcases origin with z | lo; exact Or.inl z; exact Or.inr (by omega)) heapGrowth domain (fun w hi lo => memory w lo hi),
    codesLinked.after_memory_between_cells decodedState post _ _ _ _ _ _ _ _ _ 2713715344
      ?_ ?_ (by rcases codesOrigin with z | lo; exact Or.inl z; exact Or.inr (by omega)) heapGrowth domain (fun w hi lo => memory w lo hi),
    headersLinked.after_memory_between_cells decodedState post _ _ _ _ _ _ _ _ _ 2713715344
      ?_ ?_ (by rcases headersOrigin with z | lo; exact Or.inl z; exact Or.inr (by omega)) heapGrowth domain (fun w hi lo => memory w lo hi),
    siKept,rootKept,?_,?_,domain,installed,?_,?_,outKept.trans decodedOut,?_,?_,?_⟩
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega
  · rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      using initialized key different
  · rw [domain]; exact header.payloadDomain
  · have key := memory (heap + (0#64)) (by simpa using lower) (by simp; omega)
    rw [key]
    simpa using header.payloadCell

  · refine ⟨blobLength,payloadKept.blobBound,?_,?_⟩
    · simpa [BitVec.add_assoc] using payloadKept.blobEntry.lengthDomain
    · simpa [BitVec.add_assoc] using payloadKept.blobEntry.lengthCell
  · omega
  · omega
#print axioms main_vm_entry_payload_extra_reach
end InitECandidate.Runtime
