# Source-domain applicability

The challenge fixes `sourceInitialState.memaddrs = ordinaryDomain` in
`InitE/SourceSemantics.lean`. This is `StackRemove.addresses`, containing only
8-aligned ordinary word cells above `sourceBase`; it is preserved by evaluation.
It does not contain every byte address below the heap limit.

Existing generic runtime/world lemmas with premises such as
`∀ a, a.toNat < 33806089496 → state.memaddrs a`, or word-domain membership for
every consecutive byte offset of a key, cannot be instantiated at the actual
challenge state. Their generic proofs do not establish that applicability.
They must not be used as a completed actual source bound until these premises
are weakened to the accessed aligned cells, or a domain-extension simulation
and the required transfer back to the actual evaluator are proved.

Byte reads require the containing aligned cell. Unaligned input keys also need
the original hash/memeq byte fallback proofs. Neither an unaligned word's value
nor its accessibility can be inferred from the assembled bytes alone.

The statement-46 withdrawal-loop window theorem has no all-byte-domain premise,
but still requires its concrete entry geometry and the statement-47 tail.
`Solution.claimedScore` remains infinity; the finite certificate is unfinished.
