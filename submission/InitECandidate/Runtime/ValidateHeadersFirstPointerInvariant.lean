import InitECandidate.Runtime.ValidateHeadersFirstInvariantStep
import InitECandidate.Runtime.ValidateHeadersFirstBodyPointerPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Concrete runtime invariant plus initialized header pointers and the
frontier bound protecting the complete pointer buffer during later decodes. -/
def ValidateHeadersFirstPointerInvariant {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ValidateHeadersFirstInvariant e s rank ∧
  (∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    HeaderPointerPrefix s e.hs index.toNat) ∧
  (∃ heap : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    e.hs.toNat + e.count.toNat * 8 ≤ heap.toNat)

/-- A successful enabled actual iteration re-establishes every concrete
runtime premise, with a strictly smaller natural rank. -/
theorem validate_headers_first_pointer_invariant_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (completeValid : ValidateHeadersFirstPointerInvariant e s rank) (code : s.code = originalRuntimeCode)
    (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ValidateHeadersFirstPointerInvariant e post nextRank := by
  obtain ⟨valid,⟨prefixIndex,atPrefixIndex,initialized⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩ := completeValid
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
  have indexEq : prefixIndex = index :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atPrefixIndex.symm.trans i)))
  subst prefixIndex
  have initializedNext := validate_headers_first_body_pointer_prefix s post e.array e.count index pointer length
    e.input e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
    arr i entry table e.inputBound e.inputAfter inputBefore e.tableAbove tableBefore (by have := e.inputCap; omega)
    scratch frame code e.orderedFrame e.framePositive e.scratchBelow arena heapGlobal heapBound
    (by have := e.inputCap; omega) heapArena e.ceilingAligned hs hashes inside e.tableBeforeHs e.hsBufferBound
    e.hashBufferBound e.hashAligned e.inputCap state pad budget e.hsBeforeHashes e.stateBelow e.padBelow
    (by rw [sameHeap]; omega) initialized hsAbove bufferBeforeHashes (by rw [sameHeap]; exact bufferBefore) normal
  have progress := validate_headers_index_progress index e.count inside
  refine ⟨nextRank,smaller,invariant,⟨index + 1,increment,?_⟩,finalHeap,finalHeapGlobal,?_⟩
  · rw [progress.1]
    exact initializedNext
  · rw [← sameHeap] at bufferBefore
    omega

#print axioms validate_headers_first_pointer_invariant_step
end InitECandidate.Runtime
