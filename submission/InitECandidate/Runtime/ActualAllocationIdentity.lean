import InitECandidate.Runtime.ActualAllocationFree
import InitECandidate.Proofs.BackendStages.Alloc

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.BackendStages

/-- Allocation lowering preserves every actual body; the only code addition
is the compiler's standard GC stub. This does not itself prove GC unreachable. -/
theorem actual_allocated_code : Alloc.stack =
    StackAlloc.stubs RiscVConfig.pancakeRiscVBackendConfig.dataConf ++ Raw.stack := by
  rw [← Alloc.compile_eq, StackAlloc.compile, actual_allocation_map]

#print axioms actual_allocated_code
end InitECandidate.Runtime.StackAlloc
