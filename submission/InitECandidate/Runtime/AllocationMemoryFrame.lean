import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.OriginalAllocationCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original allocator body performs no memory store, so every outcome of it keeps memory
and globals exactly as they were. -/
theorem alloc_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_alloc) = true := by
  rw [source_alloc_body]
  rfl

theorem alloc_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_alloc) :=
  memoryFrame_leaf _ alloc_readOnly

/-- Memory at any cell, and the global map, survive any original allocator call. -/
theorem alloc_call_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) (w : BitVec 64) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_alloc)).2.memory w = s.memory w := by
  rw [(alloc_memoryFrame s code).1]

#print axioms alloc_memoryFrame
#print axioms alloc_call_memory
end InitECandidate.Runtime
