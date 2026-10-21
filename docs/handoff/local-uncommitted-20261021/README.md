# Additional local work preserved at shutdown

These patches and drafts were uncommitted in older checkouts. They are retained for reuse, not integrated into the proof build or challenge. No fresh Lean check or runtime verification was run for them. Apply patches against their original base revisions below; proof draft files retain .lean.txt extensions deliberately.

- root-tooling: original checkout `.`, base `1ac86616d6af633f734c1b50b2d65bcc267d4ae5`.
- withdrawal-proof: original checkout `work/finite-flash-checkout`, base `3b8f13d6d595ed4cc306f2f321067e6ee820fd30`.
- exponentiation-proof: original checkout `work/finite-vm-checkout`, base `f1c2c992058f3b8066f8dde109f96e3ee20e6847`.

Root tooling patch includes EEST RSS/time limits, Spike instruction cap, historical allocation-audit clarification, and an eight-CPU verifier configuration. The latter is archived only; the participant challenge remains unchanged. Exponentiation drafts and withdrawal edits are unfinished and may have unresolved premises. Generated .olean files, local messaging rules, copied helper scripts and the local .lake symlink were discarded from their original checkouts.
