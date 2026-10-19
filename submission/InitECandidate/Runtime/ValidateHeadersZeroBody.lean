import InitECandidate.Runtime.ValidateHeadersZeroSuffix
import InitECandidate.Runtime.ValidateHeadersBuffers
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The entire original zero-header function consumes at most four source
ticks, including allocator failure. No input, witness or parser arena premise
is required; both real loops are skipped. -/
theorem runBounded_validate_headers_zero_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word (0 : BitVec 64))))
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (budget : 4 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_validate_headers) 4 := by
  rw [source_validate_headers_body]
  have allocated := validate_headers_prefix_reaches s 0 heap code atCount heapGlobal heapBound budget
  apply RunBounded.ofReaches (prefixCost := 4) (tailCost := 0) budget allocated
  intro next facts remaining
  obtain ⟨small,first,hsAllocation,hashAllocation⟩ := facts
  obtain ⟨hs,hashes,n,rest⟩ := validate_headers_buffers s first next 0 heap (by simp) atCount hsAllocation hashAllocation
  exact runBounded_validate_headers_zero_suffix next heap (allocationEnd heap (validateHeadersHsSize 0)) n hs hashes

#print axioms runBounded_validate_headers_zero_body
end InitECandidate.Runtime
