# Source-domain applicability

The challenge fixes `sourceInitialState.memaddrs = ordinaryDomain` in
`InitE/SourceSemantics.lean`. This is `StackRemove.addresses`, containing only
8-aligned ordinary word cells above `sourceBase`; it is preserved by evaluation.
It does not contain every byte address below the heap limit.

Generic runtime/world lemmas requiring every byte address below 33806089496
must be instantiated on `expandedRuntimeEntry`, rather than directly on the
ordinary challenge state. `expanded_runtime_bounded_arena` in `ExpandedRuntimeDomain`
provides this premise, and `expanded_runtime_domain_contains` proves inclusion
of the actual domain in the expanded domain.

The existing `evaluateHOLFiniteState_memaddrs_mono` in `PanDomainEvaluation` theorem
preserves every non-error evaluation when its memory domain is enlarged.
`sourceBound_of_expanded_non_timeout` in `SourceBoundFromExpanded` uses this theorem
by contradiction: a timeout on the actual state would also be a timeout on the
expanded state. `ExpandedMainCallBoundReduction` reduces the source certificate
to a no-timeout bound on `mainAt 0`, adding the main-call entry tick. Thus a
complete domain bridge already exists; the remaining obligation is a concrete
bound for the entire expanded main body. Its 16-module bridge/reduction closure
was independently replayed in `work/existing-domain-bridge-root-review`.

Byte reads require the containing aligned cell. Unaligned input keys still need
the original hash/memeq byte fallback proofs; domain enlargement alone does not
prove alignment or an unaligned word value from assembled bytes. Separately,
old unsatisfiable `hkoWs` premises must be replaced by the applicable repaired
workspace invariants before their bounds can contribute to the certificate.

The statement-46 withdrawal-loop window theorem has no all-byte-domain premise,
but still requires its concrete entry geometry and the statement-47 tail.
`Solution.claimedScore` remains infinity; the full runtime bound, quantitative
compiler transfer, and finite certificate are unfinished.
