# Memory framing

The small fixed-footprint layer in `WordSeparation` preserves predicates using actual execution write effects and disjoint semantic word cells. Byte buffers use containing word addresses, including unaligned slices. `TriePathBufferFieldsFrame` handles path cells; `TrieStoredHeaderFrame` shares record geometry between path and allocation-floor preservation.

Existing theorem signatures are unchanged. Actual source execution must still establish its write effect. Allocation, changing key headers, and trie acyclicity require explicit invariants; the frame rule does not supply them.

Integrated after isolated experimental replay. The canonical eight-module check is recorded in `work/separation-integration-root/verdict.json`; the concrete child-link floor check in `work/trie-floor-store-root/verdict.json`; the insertion/root-store mixed closure in `work/mixed-runtime-131-root/verdict.json`. These are Lean proof checks, not a final finite-score verifier verdict. Separating conjunction and points-to are optional primitives; present consumers primarily use snapshots and the frame rule.

## Incremental separation plan

`TrieOwnedFootprint` conservatively covers record addresses and the containing word cells of actual stored key buffers. The frozen reference memory fixes both their values and their footprint. Shared key slices may overlap within this ownership set; only the separate scratch region must be disjoint. Payload buffers are outside this definition.

`trieScratch` packages the two snapshots using separating conjunction. `trieScratch_preserves` consumes the packaged separation and an explicit `WritesOnly` execution effect once to transport the allocated world, kind tags, stored paths, and allocation floor together. Globals, memory domain, and byte order remain explicit context facts. `trieScratch_write_word` derives its write effect from the concrete `sourceWriteWord` operation.

Fresh allocation uses ownership extension rather than treating a new record as an unrelated scratch write. `trieOwnedFootprint_extend` states the geometric obligations; `NodeNewLeafDeclarationReady.owned_footprint_extension` discharges them from the actual constructor witness and old allocation geometry. New path/content facts remain the responsibility of the existing constructor proofs. Extension and branch allocation instances and further composition refactors are incremental follow-up work.
