# Finite-score fleet preservation snapshot

Work paused at user request for challenge rework. This branch merges coordinator f3914600c, source af7b8b43f, native padding e5a6fd06d, candidate guest 71580648c, and indexed colouring e400815f9. All agents confirmed STOPPED.

This is a WIP archive, not a verified finite-score submission. Individual checked results and open premises are described in agent handoffs: docs/cost-add-path/HANDOFF-finite-auth.md, submission/docs/handoff-native-padding-direct.md, work/HANDOFF_finite-vm.md, docs/handoff/finite-claude4-colouring.md. Unverified drafts remain explicitly parked. No full build or verifier was run after these merges.

Conflict resolution: latest source-agent cost-model versions retained over earlier coordinator copies; source-agent renamed CrepSharp modules retained; shared candidate/source conflicts retain the integrated source-model versions; FullSSATableTailCost retains the coordinator version. All original alternatives remain reachable through merge parents. No challenge changes were introduced by conflict resolution.

Finite score and whole compiler/guest composition remain unproved. Tight source ADD diagnostic was corrected to 13447 before SSA, leaving only 53 against the 13500 allowance; do not reuse earlier 12259 estimate. Function-indexed colouring theorem is checked in the agent tree; global integration remains open. Native per-section certificates do not yet give the final aggregate fetched bound.
