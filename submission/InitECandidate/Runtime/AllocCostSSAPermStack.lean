import InitECandidate.Runtime.AllocCostSSATransport

/-!
# Stack-permutation work transport (re-export)

The `PERM_STACK` executed-work transport for the old (price-free) counter is
proved, for every program constructor, as `wordPathWork_permStack_variant` in
`InitECandidate.Runtime.AllocCostSSATransport`.  That module also provides
`decClock_stack_permute`.

This file used to carry an earlier, independent draft of the same theorem.  It
is now a thin re-export so that the import chain through
`AllocCostSSACallAlignment` is unchanged and there is a single checked proof of
the transport statement.
-/
