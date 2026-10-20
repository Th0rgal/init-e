import InitECandidate.Runtime.ValidateHeadersParentReaches
/-!
Rank-aware constant room for the validation loop.

The decode call needs 624 bytes of heap room.  A plain `heap + 624 ≤ cap` component cannot be an
invariant: the heap grows by at most 624 per iteration, and `old + 624 ≤ cap` with
`new ≤ old + 624` does not give `new + 624 ≤ cap`.  What *is* an invariant is the rank-aware
version: at rank `r` the loop still has `r` iterations to run, so

  `heap + (r + 1) * 624 ≤ cap`,

which is preserved because the heap grows by at most one 624-block per iteration while the rank
drops by one.  The extra `+ 1` is the current iteration's own room.

The initial instance is derived from a concrete margin under the cap: the header count is at most
256, so reserving `(256 + 1) * 624` bytes of headroom above the heap at loop entry gives every
rank of the loop its room.  The margin `33805929128` is exactly `33806089496 - 257 * 624`; which
initial heap actually satisfies it is a fact about the caller's own entry state and is not
assumed here.
-/
namespace InitECandidate.Runtime
open Flapjack
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The heap margin that leaves room for the whole header loop: the cap less `(256 + 1) * 624`,
the headroom for at most 256 headers plus the current iteration. -/
def headerLoopHeapMargin : Nat := 33805929128

/-- **Initial rank-aware room.** A heap at loop entry below the loop's heap margin, together with
the environment's header-count bound, gives the loop's initial room: the current iteration plus
one 624-block per remaining header. -/
theorem validate_headers_initial_rank_room (heap count : Nat)
    (heapMargin : heap ≤ headerLoopHeapMargin) (countBound : count ≤ 256) :
    heap + (count + 1) * headerCarryRoom ≤ 33806089496 := by
  unfold headerLoopHeapMargin headerCarryRoom at *
  omega

/-- **Preservation of the rank-aware room.** If the current iteration's room is available at
rank `rank` and the iteration grows the heap by at most one 624-block, then the remaining rank
still has its room.  Note that the rank must be positive: at rank `0` the loop is over. -/
theorem validate_headers_rank_room_preserved (oldHeap newHeap rank : Nat)
    (room : oldHeap + (rank + 1) * headerCarryRoom ≤ 33806089496)
    (growth : newHeap ≤ oldHeap + headerCarryRoom) (rankPositive : 1 ≤ rank) :
    newHeap + ((rank - 1) + 1) * headerCarryRoom ≤ 33806089496 := by
  unfold headerCarryRoom at *
  omega

/-- Two 624-blocks are not free: the plain component fails after one iteration, which is why the
room has to be rank-aware. -/
theorem validate_headers_plain_room_not_preserved (oldHeap newHeap : Nat)
    (room : oldHeap + headerCarryRoom ≤ 33806089496) (growth : newHeap ≤ oldHeap + headerCarryRoom)
    (lastBlock : oldHeap = 33806089496 - headerCarryRoom) (blocked : newHeap = oldHeap + headerCarryRoom) :
    ¬ newHeap + headerCarryRoom ≤ 33806089496 := by
  unfold headerCarryRoom at *
  omega

#print axioms validate_headers_initial_rank_room
#print axioms validate_headers_rank_room_preserved
#print axioms validate_headers_plain_room_not_preserved
end InitECandidate.Runtime
