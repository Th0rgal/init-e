# All-outcome source cost (`CostBounded`) — manifest

New module `InitECandidate.Runtime.SourceCost` (no existing module edited):

- `CostBounded {σ} (program : ProgHOL 64) (C : Nat) : Prop` —
  `∀ state, state.clock ≤ (evaluateHOLFiniteState state program).2.clock + C`.
  This is genuinely **all-outcome**: timeouts fire only at clock `0` and keep the clock
  (`emptyLocalsHOLFinite` preserves it), errors/raises return the state clock, and a returned result
  keeps the clamped clock. No budget premise is needed for the inequality; a separate budget premise
  is only needed to exclude `some .timeOut`.
- `costBounded_zero_of_clockPreserving`, `costBounded_straightLine`: straight-line bodies cost 0
  (reuses `ClockPreserving`/`clockPreserving_of_straightLine` from `SourceClock`).
- `costBounded_mono`: a larger constant is also valid.
- `costBounded_seq`: `C1 + C2` (the `fixClockHOLFinite` clamp is the identity on any evaluated pair,
  and the evaluated clock never exceeds the entry clock).
- `costBounded_ite`: `max C1 C2` (condition failure returns the entry state, so the entry clock is the
  post clock there).

Checked GREEN with only `[propext, Classical.choice, Quot.sound]`.

## Still open on the cost side

- `dec`/`decCall`/`call`/`while` composition lemmas: a call costs `1` at entry plus its callee body's
  constant; a `while` costs at most `n * (1 + bodyCost)` when the loop runs at most `n` iterations
  (the timeout branch keeps the clock, so it never breaks the inequality).
- Then the concrete encoder: `rlp_encode_word` is straight-line in its three byte-prefix phases
  (`source_rlpEncodeWord_body`), `rlp_encode_bytes` is `rlp_write_header` + `memcpy` + return
  (`source_rlpEncodeBytes_body`), the withdrawal record is four fields with a fixed 20-byte address,
  a fixed 64-byte alloc and the short `memcpy` (`source_memcpy_scoped_body`), so the sum is a concrete
  numeral.
