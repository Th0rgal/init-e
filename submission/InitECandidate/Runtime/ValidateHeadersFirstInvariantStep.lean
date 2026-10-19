import InitECandidate.Runtime.ValidateHeadersFirstInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A successful enabled actual iteration re-establishes every concrete
runtime premise, with a strictly smaller natural rank. -/
theorem validate_headers_first_invariant_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (valid : ValidateHeadersFirstInvariant e s rank) (code : s.code = originalRuntimeCode)
    (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ValidateHeadersFirstInvariant e post nextRank := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,heapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have inside := validate_headers_first_condition_enabled s index e.count w e.cap within i n condition nonzero
  obtain ⟨pointer,length,entry⟩ := table index inside
  obtain ⟨finalHeap,finalHeapGlobal,heapMono,finalHeapBound,finalHeapAligned,scratchNext,frameNext,domain,installed,tableNext,workspace,increment⟩ :=
    validate_headers_first_body_normal_frame s post e.array e.count index pointer length e.input e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
      arr i entry table e.inputBound e.inputAfter inputBefore e.tableAbove tableBefore (by have := e.inputCap; omega)
      scratch frame code e.orderedFrame e.framePositive e.scratchBelow arena heapGlobal heapBound (by have := e.inputCap; omega)
      heapArena e.ceilingAligned hs hashes inside e.tableBeforeHs e.hsBufferBound e.hashBufferBound e.hashAligned e.inputCap state pad budget
      e.hsBeforeHashes e.stateBelow e.padBelow normal
  have progress := validate_headers_index_progress index e.count inside
  refine ⟨e.count.toNat - (index + 1).toNat,by omega,index + 1,finalHeap,?_,?_,increment,?_,?_,progress.2.1,rfl,tableNext,
    by omega,by omega,scratchNext,frameNext,finalHeapGlobal,?_,?_,finalHeapBound,?_,?_⟩
  · exact (validate_headers_first_body_local_frame s post _ (by decide) (by decide) normal).trans arr
  · exact (validate_headers_first_body_local_frame s post _ (by decide) (by decide) normal).trans n
  · exact (validate_headers_first_body_local_frame s post _ (by decide) (by decide) normal).trans hs
  · exact (validate_headers_first_body_local_frame s post _ (by decide) (by decide) normal).trans hashes
  · rw [workspace (ofString "keccak_st") (by decide)]; exact state
  · rw [workspace (ofString "keccak_pad") (by decide)]; exact pad
  · intro address lo hi
    rw [domain]
    exact arena address lo hi
  · intro address lo hi
    rw [domain]
    exact heapArena address (by omega) hi

#print axioms validate_headers_first_invariant_step
end InitECandidate.Runtime
