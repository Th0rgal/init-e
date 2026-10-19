import InitECandidate.Runtime.ValidateHeadersFirstInvariantStep
import InitECandidate.Runtime.ValidateHeadersFirstBodyWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A successful enabled actual iteration re-establishes every concrete
runtime premise, with a strictly smaller natural rank. -/
theorem validate_headers_first_invariant_window_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (initialHeap : BitVec 64)
    (valid : ValidateHeadersFirstInvariant e s rank) (code : s.code = originalRuntimeCode)
    (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (initialBinding : s.globals.lookup (ofString "heap_ptr") = some (.val (.word initialHeap)))
    (bufferBefore : e.hs.toNat ≤ initialHeap.toNat)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    (∀ address : BitVec 64, e.ceiling ≤ address.toNat → address.toNat < e.hs.toNat → post.memory address = s.memory address) := by
  obtain ⟨index,heap,arr,n,i,hs,hashes,within,distance,table,inputBefore,tableBefore,scratch,frame,heapGlobal,state,pad,heapBound,arena,heapArena⟩ := valid
  have inside := validate_headers_first_condition_enabled s index e.count w e.cap within i n condition nonzero
  obtain ⟨pointer,length,entry⟩ := table index inside
  have sameHeap : heap = initialHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapGlobal.symm.trans initialBinding)))
  exact validate_headers_first_body_window s post e.array e.count index pointer length e.input e.inputLength e.scratch e.frame heap e.hs e.hashes e.keccakState e.keccakPad e.ceiling e.inputLimit
      arr i entry table e.inputBound e.inputAfter inputBefore e.tableAbove tableBefore (by have := e.inputCap; omega)
      scratch frame code e.orderedFrame e.framePositive e.scratchBelow arena heapGlobal heapBound (by have := e.inputCap; omega)
      heapArena e.ceilingAligned hs hashes inside e.tableBeforeHs e.hsBufferBound e.hashBufferBound e.hashAligned e.inputCap state pad budget
      e.hsBeforeHashes e.stateBelow e.padBelow (by rw [sameHeap]; exact bufferBefore) normal

#print axioms validate_headers_first_invariant_window_step
end InitECandidate.Runtime
