import InitECandidate.Runtime.MainDecoderVmEntryReach
import InitECandidate.Runtime.MainDecoderCallWitnessArrays
import InitECandidate.Runtime.WitnessArrayMemoryFrame
import InitECandidate.Runtime.WitnessSpanGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The original initial hash carries the actual decoded state/code witness
arrays to main's VM-validation continuation, with input-size bounds. -/
theorem main_witness_vm_entry_reaches {F : Type} (state ready decodedState : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,decodedState))
    (budget : 2 + (htrNewPayloadBodyCost + 1) ≤ decodedState.clock) :
    ∃ si rootHeap array count codes codeCount input length codeInput codeLength : BitVec 64,
      length.toNat ≤ 134217712 ∧ codeLength.toNat ≤ 134217712 ∧
      (count = 0 ∨ si.toNat + 88 ≤ array.toNat) ∧
      (codeCount = 0 ∨ si.toNat + 88 ≤ codes.toNat) ∧
      2713715344 ≤ si.toNat ∧
      Reaches decodedState (mainAt 21)
        (fun post =>
          WitnessArrayLinked post si 40 48 array count input length (allocationEnd rootHeap 32) ∧
          WitnessArrayLinked post si 56 64 codes codeCount codeInput codeLength (allocationEnd rootHeap 32) ∧
          post.locals.lookup (ofString "si") = some (.val (.word si)) ∧
          post.locals.lookup (ofString "root") = some (.val (.word rootHeap)) ∧
          post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd rootHeap 32))) ∧
          post.memaddrs = decodedState.memaddrs ∧ post.code = originalRuntimeCode)
        (2 + (htrNewPayloadBodyCost + 1)) (mainAt 23) := by
  obtain ⟨length,si,OW,middle,last,array,count,codes,codeCount,headers,headerCount,witnessHeap,
    small,lengthLower,owBound,middleLower,ordered,lastBound,wlocals,stateLinked,codesLinked,_,origin,codesOrigin,
    witnessBinding,_,_,_,recordExtent,readyHeap⟩ :=
    main_decoder_call_witness_arrays state ready decodedState code arena valid run
  obtain ⟨rootHeap,heap,payload,blobs,blobCount,parentRoot,record,payloadArray,payloadCount,input,inputLength,
    withdrawals,withdrawalCount,requests,requestLength,payloadBlobs,blobLength,binding,growth,header,table,
    recordAfter,decoded,finalBinding,_,cap,alignment,payloadExtent,arrayExtent,atSi,payloadOrigin,lower,workspace⟩ :=
    main_decoder_call_hash_workspace state ready decodedState code arena valid run
  have heapEq : heap = si := by
    have siLookup : decodedState.locals.lookup (ofString "si") = some (.val (.word si)) := by
      rw [wlocals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    exact lookup_word_eq decodedState _ _ _ atSi siLookup
  subst si
  have rootEq : rootHeap = witnessHeap := by
    rw [witnessBinding] at finalBinding
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj finalBinding.symm))
  subst witnessHeap
  have lenSub : (length - (2#64)).toNat = length.toNat - 2 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lengthLower)]; rfl
  have remaining : ((length - 2) - OW).toNat ≤ 134217712 := by
    change ((length - (2#64)) - OW).toNat ≤ 134217712
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def,lenSub]; exact owBound),lenSub]
    omega
  have firstSmall : (middle - (12#64)).toNat ≤ 134217712 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact middleLower)]; omega
  have codeSmall : (last - middle).toNat ≤ 134217712 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact ordered)]; omega
  have reach := main_root_initial_hash_reaches_metadata decodedState rootHeap heap payload blobs blobCount parentRoot record
    payloadArray payloadCount input inputLength withdrawals withdrawalCount requests requestLength payloadBlobs blobLength
    workspace atSi header table decoded lower growth recordAfter payloadExtent arrayExtent payloadOrigin budget
  refine ⟨heap,rootHeap,array,count,codes,codeCount,((2713731432 : BitVec 64) + 2 + OW) + (12#64),middle - (12#64),
    ((2713731432 : BitVec 64) + 2 + OW) + middle,last - middle,firstSmall,codeSmall,origin,codesOrigin,lower,?_⟩
  apply reaches_mono decodedState (mainAt 21) (mainAt 23) _ _ _ _ (le_refl _) ?_ reach
  intro post facts
  obtain ⟨_,_,_,siKept,rootKept,globals,domain,installed,memory⟩ := facts
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
    siKept,rootKept,?_,domain,installed⟩
  all_goals first
    | (rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    | (constructor <;> rw [BitVec.toNat_add_of_lt (by simp; omega)] <;> simp <;> omega)

#print axioms main_witness_vm_entry_reaches
end InitECandidate.Runtime
