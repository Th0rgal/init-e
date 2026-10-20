# Lightweight memory separation experiment

Branch: `experiment/lightweight-separation`, based on `4a63fecd0`.
This is an isolated participant-proof experiment. It does not change executable source, the challenge, or the claimed score.

`WordSeparation` defines assertions with fixed word-address footprints, separating conjunction, points-to, snapshots, write effects, and a proved frame rule. Byte buffers use their actual containing word addresses; disjoint byte ranges alone are insufficient for this memory model.

The shared `TriePathBuffer.after_record_fields` theorem applies the frame rule to the actual record-field write effect. Its statement is unchanged. Payload transport, node-path framing, and cache invalidation now share this theorem. Their existing execution and geometry premises remain explicit; no successful callee outcome or runtime bound is introduced as an assumption.

The three existing modules shrink by 40 lines in total (58 removed, 18 added). This includes moving the existing helper into its own module. The new abstraction and helper add more lines than this initial saving: this is a composition experiment, not a net source-size reduction. The useful result is that the cache/path consumers no longer repeat the containing-cell arithmetic. Separating conjunction and points-to are available but are not yet used by these consumers; the demonstrated benefit currently comes from the snapshot frame rule and shared geometry lemma.

Validation: all five changed/new modules passed independent Lean 4.33.1 kernel replay in a private artifact directory. A mixed import check also loaded the existing indexed-insertion assignment and root-store endpoints against the experimental modules. Printed theorem axioms contain only `propext`, `Classical.choice`, and `Quot.sound`. Sources and hashes were frozen in `work/separation-root-review` in the development workspace. This is not a full finite-score verifier run.

Limitations: footprints are fixed rather than existentially split heaps. Allocation, changing registries, ownership transfer, and acyclic trie bounds still need explicit invariants. The frame rule preserves only predicates proved insensitive to other cells; it does not derive execution effects. Keep this branch separate while assessing whether additional compositions justify its framework overhead.

## Follow-up evaluation

The next finite-score obligation supplied a second concrete client: allocation-floor preservation under record-field writes. `TrieStoredHeaderFrame` now shares the exact header-disjointness proof between that client and path preservation. The experiment includes fresh leaf/extension/branch floor lemmas to check this composition. Nine proof modules plus the mixed integration check pass private kernel replay with only the standard axioms listed above.

Recommendation: reuse the small footprint/frame layer and geometry helpers when integrating these invariants. Evidence supports shared framing; it does not yet justify a larger separation-logic encoding. The exported header helper itself is ordinary geometric factoring, while path-cell transport uses the footprint frame rule. Keep those benefits distinct. Fresh allocation and mutable key headers need explicit ownership-growth/transfer lemmas before they can benefit similarly. No claim is made that this solves acyclicity or the final runtime bound.
