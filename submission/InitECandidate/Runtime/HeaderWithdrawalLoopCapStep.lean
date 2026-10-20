import InitECandidate.Runtime.HeaderWithdrawalEntryFacts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- **Dynamic heap-cap step, from an actual normal allocation return.** If the current heap pointer plus
one 64-byte cell still fits under the allocator cap, then the *successor* heap pointer produced by that
allocation also fits under the cap. This is the per-iteration content of the capped-heap invariant: it is
stated about the real `allocationEnd` of the real allocator, not about a pre-reserved run of future
allocations. A failed allocation never produces this successor at all (it raises), so it contributes no
case here and exits the loop through `StAbort`. -/
theorem allocationEnd_cap_step (pointer : BitVec 64) (cap : Nat)
    (aligned : pointer.toNat % 8 = 0)
    (bounded : pointer.toNat + 64 ≤ cap) (capSmall : cap ≤ 33806089496) :
    (allocationEnd pointer 64).toNat ≤ cap := by
  have covered : pointer.toNat + (64#64 : BitVec 64).toNat ≤ 33806089496 := by
    show pointer.toNat + 64 ≤ 33806089496
    omega
  have exact := allocationEnd_aligned_toNat pointer 64 covered aligned (by decide)
  rw [exact]
  show pointer.toNat + 64 ≤ cap
  omega

/-- The same step on the loop's own heap chain: a normal successful allocation of the `j`-th cell takes the
capped heap to the `(j+1)`-th word, which is again capped. Only the *current* bound and the *successful*
allocation's end are used; no statement about any later iteration is required. -/
theorem wdHeapWord_cap_step (base : BitVec 64) (j cap : Nat)
    (succ : wdHeapWord base (j + 1) = allocationEnd (wdHeapWord base j) 64)
    (aligned : (wdHeapWord base j).toNat % 8 = 0)
    (current : (wdHeapWord base j).toNat + 64 ≤ cap) (capSmall : cap ≤ 33806089496) :
    (wdHeapWord base (j + 1)).toNat ≤ cap := by
  rw [succ]
  exact allocationEnd_cap_step (wdHeapWord base j) cap aligned current capSmall

/-- Consequence for the loop invariant: the `frontier` fact needed at iteration `k` is implied by the
capped heap at `k` alone, so the loop never needs room reserved for future iterations. -/
theorem wdHeapWord_frontier_of_cap (base : BitVec 64) (j cap : Nat)
    (current : (wdHeapWord base j).toNat + 64 ≤ cap) (capSmall : cap ≤ 33806089496) :
    (wdHeapWord base j).toNat ≤ 33806089496 := by
  omega

#print axioms allocationEnd_cap_step
#print axioms wdHeapWord_cap_step
#print axioms wdHeapWord_frontier_of_cap
end InitECandidate.Runtime
