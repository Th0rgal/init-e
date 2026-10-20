import InitECandidate.Runtime.ExpandedMainInitializers
import InitECandidate.Proofs.AllocationFacts
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.PanSemStateFiniteExact

/-- The proof domain really enlarges the unchanged canonical source domain. -/
theorem expanded_runtime_domain_contains (input : Guest.InputBlob) (address : BitVec 64)
    (ordinary : (canonicalOriginalSourceEntry input).memaddrs address) :
    (expandedRuntimeEntry input).memaddrs address := by
  rw [canonical_original_source_fields] at ordinary
  exact ordinaryDomain_below_top address ordinary

/-- Every proof-domain address is still below the actual heap ceiling, so
contracts with an explicit upper memory fence remain applicable. -/
theorem expanded_runtime_domain_fence (input : Guest.InputBlob) (address : BitVec 64)
    (member : (expandedRuntimeEntry input).memaddrs address) : address.toNat<heapEnd := member

theorem expanded_runtime_fence_small : heapEnd+8≤2^62 := by decide

/-- The enlarged domain supplies exactly the byte-address arena assumptions
used by the component bounds, provided their upper ceiling is the heap cap. -/
theorem expanded_runtime_bounded_arena (input : Guest.InputBlob) (address : BitVec 64)
    (below : address.toNat<33806089496) : (expandedRuntimeEntry input).memaddrs address := below

#print axioms expanded_runtime_domain_contains
#print axioms expanded_runtime_domain_fence
#print axioms expanded_runtime_fence_small
#print axioms expanded_runtime_bounded_arena
end InitECandidate.Runtime
