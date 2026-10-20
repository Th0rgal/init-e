import InitECandidate.Runtime.MainDecoderInputSpan
import InitECandidate.Runtime.WitnessBlobSpanGeometry
import InitECandidate.Runtime.MainDecoderEntryFields
import InitECandidate.Runtime.MainStatelessCallNormalResult
import InitECandidate.Runtime.StatelessBodyReturnedWitnessHeaderOrigin
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Main’s actual handled decoder call exports all three linked witness arrays. -/
theorem main_decoder_call_outer_witness_arrays {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∃ length heap array count codes codeCount headers headerCount finalHeap : BitVec 64,
      length.toNat≤134217712 ∧
      ready.locals.lookup (ofString "inp")=some (.rStruct [.val (.word 2713731432),.val (.word length)]) ∧
      2713731432+length.toNat≤finalHeap.toNat ∧
      2713731432+length.toNat≤heap.toNat ∧
      post.locals = ready.locals.update (ofString "si",.val (.word heap)) ∧
      WitnessArrayLinked post heap 40 48 array count 2713731432 length finalHeap ∧
      WitnessArrayLinked post heap 56 64 codes codeCount 2713731432 length finalHeap ∧
      WitnessArrayLinked post heap 72 80 headers headerCount 2713731432 length finalHeap ∧
      (count = 0 ∨ heap.toNat + 88 ≤ array.toNat) ∧ (codeCount = 0 ∨ heap.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ heap.toNat ≤ finalHeap.toNat ∧ heap.toNat + 96 ≤ finalHeap.toNat ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      (headerCount = 0 ∨ heap.toNat + 88 ≤ headers.toNat) := by
  obtain ⟨length,_,_,heap,inp,_,_,small,fits,offsets,atHeap,capped,aligned,lower,installed,domain,_,_⟩ := valid.fields
  obtain ⟨value,bodyPost,bodyRun,_,resumed⟩ :=
    main_stateless_call_normal_result ready post 2713731432 length inp (installed.trans code) run
  let entry := callEntryStateHOLFinite ready (statelessInputCallee 2713731432 length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word 2713731432)) := by
    simp [entry,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have cells : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)),
      entry.memaddrs ((2713715344 : BitVec 64) + offset) := by
    intro offset member
    change ready.memaddrs _
    rw [domain]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals exact arena _ (by decide) (by decide) (by decide)
  obtain ⟨OW,middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,owBound,lengthLower,lowerMiddle,ordered,lastBound,
    valueEq,stateLinked,codesLinked,headersLinked,origin,codesOrigin,binding,cap,al,growth,recordExtent,_,headerOrigin⟩ :=
    stateless_body_returned_witness_header_origin entry bodyPost 2713731432 length 2713715344 heap value
      (installed.trans code) p len offsets atHeap capped aligned
      (by intro address cellAligned lo hi; change ready.memaddrs address; rw [domain];
          exact arena address cellAligned (by omega) hi)
      ⟨cells 0 (by simp),cells 8 (by simp),cells 16 (by simp),cells 24 (by simp)⟩
      (by change 2713715344 + 40 ≤ heap.toNat; omega) (by change 2713731432 + length.toNat < 2 ^ 64; exact fits)
      bodyRun
  have spans := witness_blob_span_geometry length OW middle last small lengthLower owBound lowerMiddle ordered lastBound
  have before := valid.input_before_heap length heap inp atHeap
  have stateOuter := stateLinked.within_outer bodyPost heap 40 48 array count
    (((2713731432 : BitVec 64)+2+OW)+12) (middle-12) 2713731432 length finalHeap spans.1.1 spans.1.2
  have codesOuter := codesLinked.within_outer bodyPost heap 56 64 codes codeCount
    (((2713731432 : BitVec 64)+2+OW)+middle) (last-middle) 2713731432 length finalHeap spans.2.1.1 spans.2.1.2
  have headersOuter := headersLinked.within_outer bodyPost heap 72 80 headers headerCount
    (((2713731432 : BitVec 64)+2+OW)+last) (((length-2)-OW)-last) 2713731432 length finalHeap spans.2.2.1 spans.2.2.2
  have memory : post.memory = bodyPost.memory := by rw [resumed]; rfl
  have addresses : post.memaddrs = bodyPost.memaddrs := by rw [resumed]; rfl
  have globals : post.globals = bodyPost.globals := by rw [resumed]; rfl
  refine ⟨length,heap,array,count,codes,codeCount,headers,headerCount,finalHeap,
    small,inp,(by omega),before,?_,
    stateOuter.after_frame bodyPost post _ _ _ _ _ _ _ _ addresses memory,
    codesOuter.after_frame bodyPost post _ _ _ _ _ _ _ _ addresses memory,
    headersOuter.after_frame bodyPost post _ _ _ _ _ _ _ _ addresses memory,origin,codesOrigin,?_,cap,al,growth,recordExtent,atHeap,headerOrigin⟩
  · rw [resumed,valueEq]; rfl
  · rw [globals]; exact binding

#print axioms main_decoder_call_outer_witness_arrays
end InitECandidate.Runtime
