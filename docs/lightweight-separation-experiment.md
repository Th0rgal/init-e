# Lightweight memory separation experiment

Branch: `experiment/lightweight-separation`, based on `4a63fecd0`.
This is an isolated participant-proof experiment. It does not change executable source, the challenge, or the claimed score.

`WordSeparation` defines assertions with fixed word-address footprints, separating conjunction, points-to, snapshots, write effects, and a proved frame rule. Byte buffers use their actual containing word addresses; disjoint byte ranges alone are insufficient for this memory model.

The shared `TriePathBuffer.after_record_fields` theorem applies the frame rule to the actual record-field write effect. Its statement is unchanged. Payload transport, node-path framing, and cache invalidation now share this theorem. Their existing execution and geometry premises remain explicit; no successful callee outcome or runtime bound is introduced as an assumption.

The three existing modules shrink by 40 lines in total (58 removed, 18 added). This includes moving the existing helper into its own module. The new abstraction and helper add more lines than this initial saving: this is a composition experiment, not a net source-size reduction. The useful result is that the cache/path consumers no longer repeat the containing-cell arithmetic. Separating conjunction and points-to are available but are not yet used by these consumers; the demonstrated benefit currently comes from the snapshot frame rule and shared geometry lemma.

Validation: all five changed/new modules passed independent Lean 4.33.1 kernel replay in a private artifact directory. A mixed import check also loaded the existing indexed-insertion assignment and root-store endpoints against the experimental modules. Printed theorem axioms contain only `propext`, `Classical.choice`, and `Quot.sound`. Sources and hashes were frozen in `work/separation-root-review` in the development workspace. This is not a full finite-score verifier run.

Limitations: footprints are fixed rather than existentially split heaps. Allocation, changing registries, ownership transfer, and acyclic trie bounds still need explicit invariants. The frame rule preserves only predicates proved insensitive to other cells; it does not derive execution effects. Keep this branch separate while assessing whether additional compositions justify its framework overhead.
