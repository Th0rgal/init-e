# Memory framing

The small fixed-footprint layer in `WordSeparation` preserves predicates using actual execution write effects and disjoint semantic word cells. Byte buffers use containing word addresses, including unaligned slices. `TriePathBufferFieldsFrame` handles path cells; `TrieStoredHeaderFrame` shares record geometry between path and allocation-floor preservation.

Existing theorem signatures are unchanged. Actual source execution must still establish its write effect. Allocation, changing key headers, and trie acyclicity require explicit invariants; the frame rule does not supply them.

Integrated after isolated experimental replay. The canonical eight-module check is recorded in `work/separation-integration-root/verdict.json`; the concrete child-link floor check in `work/trie-floor-store-root/verdict.json`; the insertion/root-store mixed closure in `work/mixed-runtime-131-root/verdict.json`. These are Lean proof checks, not a final finite-score verifier verdict. Separating conjunction and points-to are optional primitives; present consumers primarily use snapshots and the frame rule.
