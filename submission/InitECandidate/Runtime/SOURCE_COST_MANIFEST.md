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

## Concrete invariant discharge (`HeaderWithdrawalLoopCount`)

`WdLoopInv m I0 nwd pl slices read X H t` — the statement-46 loop invariant: `∃ k`,
`I0.toNat + k ≤ nwd.toNat`, the memory domain `∀ a, t.memaddrs a ↔ m a`, the counter
`i = I0 + k`, the `nwd`/`pl`/`e`/`wd_rlp_slices` bindings, `heap_ptr = H k`, the installed `code`,
`m read`, and the watched cell `memory read = word X`.

Every obligation of the loop bound is discharged from it, with no oracle and no open hypothesis:
- `wdLoopInv_heapOf` — `heap_ptr` value with `(H k).toNat ≤ 33806089496` from the frontier hypothesis;
- `wdLoopInv_fence` — the fence from the memory domain (`Fence m DF`);
- `wdLoopInv_argsOf` — the evaluated encoder argument from the watched `pl + 48` cell (`wd_slice_args`);
- `wdLoopInv_atBound` — the loop bound `nwd`;
- `wdLoopInv_noContinue` — `wdSliceLoopBody_noControl`;
- `wdLoopInv_decrease` — clock decrement;
- `wdLoopInv_counter_toNat` / `wdLoopInv_counter_succ` — the count arithmetic
  `(I0 + k).toNat = I0.toNat + k`, `(I0 + k) + 1 = I0 + (k+1)`;
- `wdLoopInv_advance` — counter advance and code preservation (`wd_slice_step_*`, metadata);
- `wdLoopInv_keep` — invariant preservation: `H (k+1) = allocationEnd (H k) 64`, memory domain
  (`evaluateHOLFiniteState_metadata`), watched cell (`wd_slice_step_window`), the remaining bindings
  (`wd_slice_step_successor`), and `I0.toNat + (k+1) ≤ nwd.toNat` from the iteration condition.

**`wdSliceLoop_count`** — the assembled statement-46 runtime bound. For `t` satisfying the invariant,
`t.code = originalRuntimeCode`, `t.locals "i" = word I0`, `I0.toNat ≤ nwd.toNat`,
`nwd.toNat + 1 < 2^63` and the fuel budget `(nwd.toNat - I0.toNat) * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ t.clock`:

`t.clock ≤ post.clock + (nwd.toNat - I0.toNat) * ((encodeWithdrawalSourceCost DF + 1) + 1)` and
`post.clock ≤ t.clock` and no timeout, where `post` is the actual result of evaluating `wdSliceLoop`.

## Entry instantiation and 44→45→46 composition (`HeaderWithdrawalLoopEntry`)

`wdHeapWord_frontier` — the concrete heap chain stays inside the allocator limit.

`wdSliceLoop_count_entry` — statement 46 at its **actual entry state**, with every per-iteration
obligation derived from the source allocation/count facts rather than assumed: the frontier
(`wdHeapWord_frontier`), the per-iteration windows above the watched cell (`wd_heap_window_below`), the
slice-cell separation (`wd_slice_cells_below`), and the heap step (`wdHeapWord_succ`). The invariant is
witnessed at `k = 0` with counter `0`, memory domain `t.memaddrs` and `H = wdHeapWord loopHeap`.

`wdSliceLoop_count_alloc` — statements 44 → 45 → 46 composed at the clock level, from the
**pre-allocation** header state: the actual statement-44 allocator call (`wd_slices_alloc_entry` +
`evaluate_alloc_global_call`'s `ready.clock = state.clock - 1`) costs one tick and yields the arena
(`wd_rlp_slices` and `heap_ptr` at the exact 8-aligned end), statement 45's counter declaration is
free (`wd_loop_counter_binding`), and then statement 46's loop costs at most
`nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)`. Result:
`state.clock ≤ post.clock + 1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)`,
`post.clock ≤ state.clock`, no timeout.

## Statement 43–46 as `Reaches` ending at `actualPayloadHeaderAt 47` (design, checked ingredients)

`RunBounded` on `actualPayloadHeaderAt 43` is the wrong shape: `43 = .dec "nwd" .one (load [pl+56]) 44`
and `.dec`'s body argument *is* the continuation, so it would include statements 47+ (and the builder
callee). The right shape is `Reaches` (`StatelessReach`), whose `cont` argument truncates the run:

`Reaches s (actualPayloadHeaderAt 43) Q (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47)`

Checked ingredients, all green in this checkout:

- `wd_count_load_eval` — the exact `@evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable
  (s.memaddrs a))` hypothesis shape that `Reaches.reaches_dec` / `RunBounded.decWord` expect, so no
  manual `toExact` instance expansion is needed.
- `reaches_dec s "nwd" (load [pl+56]) (actualPayloadHeaderAt 44) P43` — gives the 43 prefix with `K = 0`
  and, crucially, `scoped_restore` absorbs the `resVarEq`/locals difference that makes the *pair*
  equality false (this is the routine seam now closed at the framework level).
- `wd_slice_alloc_entry` / `evaluate_alloc_global_call` (`ready.clock = state.clock - 1`) —
  `reaches_seq` data for statement 44 (`= (none, ready)`).
- `wd_loop_counter_binding` — statement 45 `.dec "i" .one (const 0)` is a `reaches_dec` step with `K = 0`.
- `wdSliceLoop_count` / `wdSliceLoop_count_alloc` — the loop bound with the real count and the installed
  encoder cost, including `state.clock ≤ post.clock + n` and `post.clock ≤ state.clock`.
- `HeaderWithdrawalLoopFrame` — `actualPayloadHeaderAt 46 = .seq wdSliceLoop (actualPayloadHeaderAt 47)`,
  so `reaches_seq` with `cont = actualPayloadHeaderAt 47` is the composition at the 46/47 seam.

The one gap between the checked ingredients and the `Reaches` statement: `reaches_seq` needs the first
part to *complete normally* (`evaluateHOLFiniteState s first = (none, t)`), while the loop bound delivers
its `RunBounded` projections plus `≠ some .timeOut`; the error branch must therefore be routed into
`Reaches`' second disjunct (`StAbort`) — i.e. one of (a) an error-free loop hypothesis (the header block
assumes the encoder succeeds), or (b) a `StAbort`-of-loop lemma. The rest is `reaches_trans`/`reaches_mono`
plumbing with `Q` the loop-exit predicate (`WdLoopInv` at exit, `i = nwd`).

## LANDED: statements 43 → 46 as `Reaches` to `actualPayloadHeaderAt 47` (`HeaderWithdrawalLoopReaches`)

- `not_returned_of_control`, `decCall_noReturn`, `wdSliceLoopBody_noReturn`, `wdSliceLoop_noReturn` —
  the loop (and its `decCall` body) never returns a value out of the enclosing function, by the same
  case analysis as `decCall_noControl` with `.returned` in place of `.continue`.
- `wd_slice_size_args` — the statement-44 allocator argument `nwd * 16 + 16` evaluates to the size.
- `wdSliceLoop_reaches` / `payloadHeader46_reaches` — the statement-46 `Reaches` seam:
  `Reaches t (.seq wdSliceLoop (actualPayloadHeaderAt 47)) Q (nwd.toNat * ((cost + 1) + 1)) 47`,
  by `reaches_seq_of_runBounded` with `bound := wdSliceLoop_count_entry` (the `RunBounded` projections)
  and `noReturn := wdSliceLoop_noReturn`. Non-returning outcomes go to `StAbort`; only normal exit
  states must satisfy `Q`. No encoder-success premise.
- **`payloadHeader43_reaches`** — the composition:
  `Reaches s (actualPayloadHeaderAt 43) (fun _ => True)
     (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47)`
  built from `reaches_dec` for 43 (`wd_count_load_eval`, `K = 0`), `reaches_seq` for 44 (the allocator
  call with `ready.clock = state.clock - 1`, `K = 1`), `reaches_dec` for 45 (`K = 0`), and the 46 seam,
  glued by `reaches_trans`/`reaches_mono`. `scoped_restore` absorbs the `resVarEq`/locals difference of
  the `.dec` steps, which is why no pair equality is needed. The builder callee after 47 is untouched.

## LANDED: `WdLoopInv` survives normal loop exit; statement-46 seam carries it (`4fe24855f`)

- `countedWhile_exit` — a counted `while (counter < boundName)` that completes normally preserves `P`:
  `P` at entry, `keep` per normally completing iteration, counter `advance`, `noContinue`, `noBreak`,
  clock-insensitivity (`decrease`) ⇒ `P` at the normal exit state, for any remaining-iteration count.
  Terminal outcomes (`.break`, `.timeOut`, `.returned`, encoder errors) are excluded by the normality
  hypothesis, so this lemma takes **no callee-success or `normalInv` oracle**. The `fixClockHOLFinite`
  wrapper of the while semantics is handled by rewriting `fixClockHOLFinite_evaluateState` on *both* the
  goal and the normality hypothesis (the clock-insensitivity premise `decrease` is what makes the
  transported predicate legitimate) — this is the seam that previously blocked the induction.
- `wdLoopInv_decClock` — `WdLoopInv` has no clock conjunct, so it descends a clock tick.
- `wdSliceLoopInv_exit` — instantiation: from the loop-entry `WdLoopInv`, any **normal** exit state of
  `wdSliceLoop` still satisfies `WdLoopInv` (pl/nwd bindings, `e` freshness, `wd_rlp_slices` pointer,
  `code`, memory domain, watched `pl+48` cell, and a final heap frontier `wdHeapWord loopHeap k` for a
  reached `k ≤ nwd.toNat`), using `wdLoopInv_keep`/`wdLoopInv_advance`/`wdSliceLoopBody_noControl`.
- `payloadHeader46_reaches_exit` — statement 46 from the loop entry reaches `actualPayloadHeaderAt 47`
  within `nwd.toNat * ((cost+1)+1)` ticks with postcondition **the full `WdLoopInv`**, replacing the
  `True` postcondition of `payloadHeader46_reaches` for the builder's benefit.

Remaining plumbing (mechanical, not a blocker): thread that postcondition through the 43 prefix, i.e.
state `payloadHeader43_reaches` with `Q := WdLoopInv (fun a => s.memaddrs a) 0#64 nwd pl slices read X
(wdHeapWord loopHeap)` — the only extra work is the `m`-transport from the loop entry's `memaddrs` to
`s.memaddrs` (available as `ready'.memaddrs = s.memaddrs`) at the last leg of the composition.

## LANDED: 43 → 47 `Reaches` with the concrete builder-entry postcondition (`a9e9b50a7`)

- `payloadHeader43_reaches_exit` — the whole statement-43 prefix now ends at `actualPayloadHeaderAt 47`
  with the **concrete exit invariant** as postcondition, not `True`:

  `Reaches s (actualPayloadHeaderAt 43)
     (WdLoopInv (fun a => s.memaddrs a) 0#64 nwd pl loopHeap read X (wdHeapWord (allocationEnd loopHeap size)))
     (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47)`

  so a builder proof at statement 47 gets `pl`/`nwd` bindings, `e` freshness, the `wd_rlp_slices`
  pointer, `code`, the memory domain, the watched `pl + 48` cell, and a final heap frontier
  `wdHeapWord (allocationEnd loopHeap size) k` with `k ≤ nwd.toNat`, with no `normalInv` oracle: the exit
  invariant is produced by `wdSliceLoopInv_exit` from the real normal loop evaluation.
- `payloadHeader43_reaches_exit_heap` — the same endpoint with the frontier word exposed directly
  (`∃ heap, heap_ptr = heap ∧ heap.toNat ≤ 33806089496`) via `wdLoopInv_heapOf`.
- The earlier `payloadHeader43_reaches` (postcondition `True`) is preserved unchanged for the bounded
  clock-only statement.

## APPLICABILITY REPAIR: `oldSlices` is independent of the heap base (pre-44)

Source fact (review finding): `wd_rlp_slices` is a guest global initialized to `0`; statement 44's
allocator needs its *old* value only as an arbitrary word, and only *after* the call does the global hold
the new slice array (the pre-call heap base). The pre-44 theorems had specialized the old value to the heap
base, which is not implied by the source. Generalized:

- `wd_slices_alloc_entry` — new parameter `oldSlices`; `atGlobal` is `wd_rlp_slices = oldSlices` and
  `oldSlices` is passed to `evaluate_alloc_global_call`'s `oldValue` slot. `atHeap` remains the heap base.
  The post-state `wd_rlp_slices = heapBase` conclusion is unchanged (it is the allocation result).
- `wdSliceLoop_count_alloc` — same generalization (both the entry binding and the second
  `evaluate_alloc_global_call`).
- `payloadHeader43_reaches`, `payloadHeader43_reaches_exit`, `payloadHeader43_reaches_exit_heap` — carry
  an arbitrary `oldSlices : BitVec 64` with `atSlices : wd_rlp_slices = oldSlices`; the loop-entry state
  after 44 keeps `wd_rlp_slices = loopHeap`.
- `HeaderWithdrawalCountBound`'s window theorem is a caller of `wd_slices_alloc_entry` whose own hypothesis
  states the old value equals its heap base, so it passes `oldSlices := slices`; the window statement does
  not depend on the old value.

All four modules re-verified `OK` with only `[propext, Classical.choice, Quot.sound]`.

## LANDED: statement-43 entry geometry derived, single entry predicate for integration (`70b43527b`, +)

- `payloadHeader43_reaches_source` — the same 43 → 47 `Reaches` endpoint as `payloadHeader43_reaches_exit`
  but with the heap/slice geometry **derived** rather than assumed: `fit`, `limit`, `readBelow`,
  `noWrapCells`, and all four loop-geometry premises (`frontier`, `outRead`, `sliceRead`, `heapStep`) come
  from `wd_slice_size_value`, `wd_slices_alloc_end`, `wd_read_below_arena`, `wd_slice_cells_below`,
  `wd_heap_window_below`, `wdHeapWord_succ`/`wdHeapWord_toNat`. The only remaining arithmetic premise is
  the source arena cap `loopHeap.toNat + 80 * nwd.toNat + 80 ≤ 33806089496` (the shape `wd_loop_budget`
  already uses), the size no-overflow fact `nwd.toNat * 16 + 16 < 2 ^ 64`, and the payload/arena
  separation `pl.toNat + 136 ≤ loopHeap.toNat`.
- `WdHeader43Entry` — the whole statement-43 entry contract as **one predicate** (read/pl/e/oldSlices/
  heap_ptr/code/clock, the `pl+56` count cell and its value, `size`, alignment, the arena cap, the signed
  count bound, the payload/arena separation, the fence and its two numeric side conditions, the watched
  cell, and the fuel budget). This is the interface a payload-header prologue hands over.
- `payloadHeader43_reaches_entry` — from a single `entry : WdHeader43Entry s …`, statements 43–46 reach
  `actualPayloadHeaderAt 47` with the concrete `WdLoopInv` exit state at cost
  `1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)`.

## LANDED: decoder-provenance entry and prologue frame for the 43 contract (`d71ef64d6`, +)

- `payloadHeader43_reaches_decoder` — the 43 → 47 prefix with the count cell **taken from the actual
  decoder output**: from a real `RlpSliceEntry s pl 3 (input + wd) nwd` of the decoded payload struct,
  `wd_slice_count_cell` supplies `memaddrs (pl + 56)` and `memory (pl + 56) = nwd`, `wd_slice_array_cell`
  supplies the watched `pl + 48` cell whose value is the exported array pointer `input + wd` (so `X` is not
  assumed but *equals* `input + wd`), and `wd_signed_count_bound` turns the actual
  `ssz_fixed_list_count` guard (`¬ 2^63 - 1 < nwd`) plus `nwd = (balance - withdrawals) / 44` into
  `nwd.toNat + 1 < 2^63`. Conclusion: `Reaches s (actualPayloadHeaderAt 43) (WdLoopInv …) … (actualPayloadHeaderAt 47)`.
- `wdHeader43Entry_frame` — the entry contract is preserved by any prologue frame: equality of the
  `pl`/`e` locals, of the two globals, of `code` and of the memory domain, preservation of the two watched
  cells (`pl + 48`, `pl + 56`), and clock monotonicity. This is the hand-over rule for an actual preceding
  statement (e.g. the statement-42 builder call) into `payloadHeader43_reaches_entry`.

## LANDED: dynamic capped-heap 43 → 47 bound (no full-loop arena reservation)

`payloadHeader43_reaches_capped` — the same 43 → 47 `Reaches` (concrete `WdLoopInv` exit state, cost
`1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)`) with the full-loop room premise
`loopHeap + 80 * nwd + 80 ≤ cap` **removed**. Room is now:

- `bounded : loopHeap + size ≤ cap` — only the *single* statement-44 slice-array allocation;
- `room : ∀ k ≤ nwd, (allocationEnd loopHeap size) + 64 * k + 64 ≤ cap` — the dynamic capped-heap invariant
  on the actual chain, i.e. exactly the fact each successive *normal* encoder return establishes by
  advancing the pointer with one successful `allocationEnd`. A failed encoder allocation leaves through the
  loop's `RunBounded` as `StAbort`, so failure paths stay bounded with no future-room oracle.

`fit`, `limit`, `frontier`, `outRead`, `sliceRead`, `heapStep` and `noWrapCells` are all derived from
`bounded` + `room` + `fitSize`; the watched cells stay below the actual monotone heap and slice array via
`wd_read_below_arena` / `wd_slice_cells_below`.
