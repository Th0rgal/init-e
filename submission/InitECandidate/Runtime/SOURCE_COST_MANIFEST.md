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

### Probe result (checked, then removed from the tree as a scratch check)

`straightLine` of the encoder's callees, evaluated with `decide_cbv` on the authoritative bodies:
`alloc`, `rlp_write_header` and `memcpy` all evaluate to `false` — each contains calls and/or loops.
So the encoder's constant is *not* just its own call count: it is
`(1 + allocBody) + Σ_fields (1 + fieldBody) + (1 + finishBody)`, with `rlp_encode_bytes` itself paying
`1 + rlp_write_header + 1 + memcpy`, and `memcpy`'s loops paying per iteration (the withdrawal record
is four fields with a fixed 20-byte address, so the iteration counts are data-bounded by 20 and the sum
is still a concrete numeral). No supplied callee/frame/fuel oracle is used in this decomposition: every
term is the callee's own body, which is why the per-callee `CostBounded` instances are the next pieces
to land in new modules.

## Adapter to the existing `ProgBounded`/`RunBounded`/`FunBounded` machinery (`SourceCostAdapter`)

New module `InitECandidate.Runtime.SourceCostAdapter` (checked, `[propext, Classical.choice, Quot.sound]`):

- `costBounded_of_progBounded`: **`ProgBounded p C` gives the all-outcome bound** for every state with
  `code = originalRuntimeCode`. Cases on `C ≤ state.clock`: a large clock uses
  `ProgBounded`'s spent bound directly; a small clock has `state.clock < C ≤ C + post.clock` because
  the post clock is a `Nat`. No timeout case needs separate treatment.
- `costBounded_of_runBounded`: the per-state form needs no code premise.
- `costBounded_call_of_funBounded`, `costBounded_allocCall` (alloc reuse: `ProgBounded.alloc`, cost 2),
  `costBounded_seq'` (reuses `RunBounded.seq` with `nextCode.trans code`).

So no new algebra is needed for shapes, clock plumbing, loops or calls: `ProgBounded.straight`,
`ProgBounded.dec`, `ProgBounded.seq`, `ProgBounded.ite`, `ProgBounded.alloc`, `ProgBounded.call`,
`ProgBounded.tail`, `ProgBounded.decCall`, `ProgBounded.countedDec` and `RunBounded.*` all feed the
adapter.

## Exact encoder cost dependency order (bodies read from the source, not assumed)

`wdAllocTail` = `decCall "buf" alloc [64] wdDecP`; `wdDecP` = `dec "p" (buf+9) wdCall0`;
`wdCall0` = `decCall "w" rlp_encode_word [p, word0] (seq wdAssign (seq wdCall8 wdCall8Tail))`;
`wdCall8` = `call "w" rlp_encode_word [p, word8]`;
`wdCallBytes` = `call "w" rlp_encode_bytes [p, wd+16, 20]`;
`wdCall36` = `call "w" rlp_encode_word [p, word36]`;
`wdFinishTail` = `decCall "total" rlp_finish_list [buf, p] (return …)`.

`rlp_encode_word` = `seq rlpEncodeWordZero (seq rlpEncodeWordSmall rlpEncodeWordLong)`; the first two
phases are `ite` + `storeByte` + `return` (cost 0), the long phase is
`decCall "ll" rlp_be_len [w]` then `call none "rlp_put_be" [dst+1, w, ll]` then `return`.
`rlp_encode_bytes` = `seq rlpEncodeBytesPrefix rlpEncodeBytesTail`, tail =
`decCall "h" rlp_write_header [dst,128,n]` then `call none memcpy [dst+h, src, n]` then `return`.
`memcpy` already has `evaluate_memcpy_body_bounded` (cost `size/32 + size/8 + 10`, so **12** for the
fixed 20-byte address).

So the remaining per-callee obligations, in dependency order, are
`FunBounded "rlp_be_len"`, `FunBounded "rlp_put_be"` (both counted byte loops, ≤ 8 iterations for a
64-bit word), then `FunBounded "rlp_encode_word"`, `FunBounded "rlp_write_header"`,
`FunBounded "rlp_finish_list"`, `FunBounded "rlp_encode_bytes"`, and finally the record sum
`2 + Σ(1 + callee)` which is a concrete numeral. Each is a `ProgBounded` composition over the quoted
body with `ProgBounded.alloc`/`call`/`decCall`/`countedDec` — no runtime oracle anywhere.

## Statement-46 loop runtime bound (checked, `HeaderWithdrawalLoopRuntime`)

Per-iteration cost, from the **actual installed encoder** (canonical shared bound
`encode_withdrawal_body_bounded`, reused through the `ProgBounded`/`RunBounded` machinery — no new
encoder proof and no oracle):
`wdSliceLoopBody_runBounded : RunBounded t wdSliceLoopBody (encodeWithdrawalSourceCost DF + 1)`
given `code`, `Fence t.memaddrs DF`, `DF + 8 ≤ 2^62`, `33806089496 ≤ DF`, the `heap_ptr` binding with
`heap.toNat ≤ 33806089496` and the argument evaluation. The decoder `decCall` is decomposed with
explicit `bodyCost`/`tailCost` (`RunBounded.decCall (bodyCost := encodeWithdrawalSourceCost DF)
(tailCost := 0)`), the two slice stores are straight-line (`runBounded_zero_of_extStraightLine`).

Loop cost (`countedWhile_runBounded`, `countedWhile_runBounded_var`, `eval_var_condition`): a counted
while with a **state-dependent** per-iteration `RunBounded` costs `n * (cost + 1)`, where the
variable-bound form matches statement 46's `while i < nwd` (the `nwd` local is fixed by the invariant
`P`). `wdSliceLoop_runBounded` is the instantiation:
`state.clock ≤ post.clock + n * (encodeWithdrawalSourceCost DF + 2)` with
`nwd.toNat - I0.toNat = n`, and the loop never times out under that budget.

Explicit remaining obligations for the unconditional statement-46 corollary (all named, none assumed):
`P`-preservation across one iteration (heap frontier `H (j+1) = allocationEnd (H j) 64`, the
`Fence`-at-`H j` fact, `nwd`/`pl`/`slices` stability, counter advance by one, `noContinue`). The
frozen `HeaderWithdrawalLoopBody` step lemmas supply the counter/heap/code parts
(`wdSliceLoopStores_adv`, `wd_slice_step_successor`, `wd_slice_step_clock_ne`,
`wd_slice_step_outcome`); the missing piece is `Fence`-preservation of the encoder's writes.

## Import infrastructure note (reproducibility)

The canonical encoder runtime bounds (`EncodeWithdrawalCallBound`, `EncodeWithdrawalRuntimeBound`,
`RlpWritersRuntimeBound`, `RlpLengthRuntimeBounds`, `EncFenceBase`, …) live on the sibling branch
`feat/finite-score-vm` and are already built in the canonical shared build. They are *imported*
(not copied into this checkout): because Lean resolves a module in the first `LEAN_PATH` entry that
contains its prefix, the private import tree must also carry those oleans. They are symlinked from
the canonical shared build, only for modules whose sources are absent from this checkout:

```bash
python3 - <<'PY'
import os,glob
B='.../finite-score-build/.lake/build/lib/lean/InitECandidate'
OUT='.../finite-flash-work/lib/lean/InitECandidate'
SRC='.../finite-flash-checkout/submission/InitECandidate'
for p in glob.glob(B+'/**/*.olean',recursive=True):
    rel=os.path.relpath(p,B); src=os.path.join(SRC,rel[:-6]+'.lean'); dst=os.path.join(OUT,rel)
    if os.path.exists(src) or os.path.exists(dst) or os.path.islink(dst): continue
    os.makedirs(os.path.dirname(dst),exist_ok=True); os.symlink(os.path.abspath(p),dst)
PY
```

No source is shadowed (the link is only created when this checkout has no source for the module), and
the shared build is never written to. Axioms of the reused theorems are those of the canonical shared
build; every theorem *stated here* still reports exactly `[propext, Classical.choice, Quot.sound]`.

## Fence preservation is free (`HeaderWithdrawalLoopFence`)

`evaluateHOLFiniteState_metadata` gives `post.memaddrs = state.memaddrs` and `post.code = state.code`
for **every** program and every run, so:
- `fence_preserved : Fence state.memaddrs DF → Fence (evaluateHOLFiniteState state program).2.memaddrs DF`
- `code_preserved : state.code = originalRuntimeCode → post.code = originalRuntimeCode`

No encoder-specific domain proof and no heap cap are needed for fence/code preservation.

Wiring (checked): `wdSliceLoopBody_runBounded_of_invariant` discharges the per-iteration `RunBounded`
of statement 46 from an invariant supplying only (a) the `heap_ptr` value with `heap.toNat ≤
33806089496`, (b) the fence (free), (c) the evaluated argument; and
`wdSliceLoop_runBounded_of_invariant` is the statement-46 loop runtime bound with that per-iteration
hypothesis already discharged. The loop lemmas now take the clock budget in the per-iteration
hypothesis (`cost ≤ state.clock`), which is what the inductive call actually provides.

Remaining obligation for the unconditional statement-46 corollary: the invariant preservation clauses
`keep`/`advance`/`noContinue`/`decrease` plus the heap cap, which the frozen
`HeaderWithdrawalLoopBody` step facts (`wd_slice_step_successor`, `wdSliceLoopStores_adv`,
`wd_slice_step_clock_ne`, `wd_slice_step_outcome`) supply once the invariant also carries the
`pl + 48` watched cell (`wd_slice_args`).
