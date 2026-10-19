import InitECandidate.Runtime.ValidateHeadersFirstInvariantStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A successful enabled actual iteration re-establishes every concrete
runtime premise, with a strictly smaller natural rank. -/
theorem validate_headers_first_invariant_heap_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (initialHeap : BitVec 64)
    (valid : ValidateHeadersFirstInvariant e s rank) (code : s.code = originalRuntimeCode)
    (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (initialBinding : s.globals.lookup (ofString "heap_ptr") = some (.val (.word initialHeap)))
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ValidateHeadersFirstInvariant e post nextRank ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        initialHeap.toNat ≤ finalHeap.toNat := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,heapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have inside := validate_headers_first_condition_enabled s index e.count w e.cap within i n condition nonzero
  obtain ⟨pointer,length,entry⟩ := table index inside
  obtain ⟨finalHeap,finalHeapGlobal,heapMono,finalHeapBound,finalHeapAligned,scratchNext,frameNext,domain,installed,tableNext,workspace,increment⟩ :=
    validate_headers_first_body_normal_frame s post e.array e.count index pointer length e.input e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
      arr i entry table e.inputBound e.inputAfter inputBefore e.tableAbove tableBefore (by have := e.inputCap; omega)
      scratch frame code e.orderedFrame e.framePositive e.scratchBelow arena heapGlobal heapBound (by have := e.inputCap; omega)
      heapArena e.ceilingAligned hs hashes inside e.tableBeforeHs e.hsBufferBound e.hashBufferBound e.hashAligned e.inputCap state pad budget
      e.hsBeforeHashes e.stateBelow e.padBelow normal
  have sameHeap : heap = initialHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapGlobal.symm.trans initialBinding)))
  have complete : ∃ nextRank, nextRank < rank ∧ ValidateHeadersFirstInvariant e post nextRank := by
    exact validate_headers_first_invariant_step e s post rank ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,heapGlobal,state,pad,heapBound,arena,heapArena⟩ code w condition nonzero budget normal
  obtain ⟨nextRank,smaller,invariant⟩ := complete
  exact ⟨nextRank,smaller,invariant,finalHeap,finalHeapGlobal,by rw [← sameHeap]; exact heapMono⟩

#print axioms validate_headers_first_invariant_heap_step
end InitECandidate.Runtime
