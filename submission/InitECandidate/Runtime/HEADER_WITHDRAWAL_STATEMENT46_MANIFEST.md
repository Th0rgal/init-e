# Statement 46 (payload-header withdrawal slice loop) — review manifest

Branch `feat/finite-score-flash`. All modules below are checked GREEN by
`./pcheck.sh Runtime.<Module>` in `work/finite-flash-work`, each printing
`AXIOMS … [propext, Classical.choice, Quot.sound]` and no `sorry`/`native_decide`.
Nothing is stubbed; the only composition premise left is the statement 47 tail, which is
root-owned.

## Frozen commits (oldest → newest)

| commit | module | content |
| --- | --- | --- |
| `5029a839c` | `RlpWithdrawalGlobalsFuel` | fuel-free copies of the encoder global lemmas: `rlpEncodeWithdrawal_returned_globals_fuel`, `rlpEncodeWithdrawal_heap_fuel`, `rlpEncodeWithdrawal_other_globals_fuel`. The `2 ≤ clock` hypothesis of the original `rlpEncodeWithdrawal_returned_globals` is *never used* in its proof (old lines 76–100), so the copies replay it without any clock premise. |
| `1d4274d1c` | `HeaderWithdrawalLoopBody` | `wd_slice_step_window` (fuel-free per-iteration memory window, clock hypothesis removed), `wd_slice_step_clock_ne` (a **normal** `decCall` run forces `t.clock ≠ 0`, via `evaluateHOLFiniteState_decCall_clock_zero`), `wd_slice_step_outcome`, `wd_slice_step_successor` (six successor facts incl. `heap_ptr = allocationEnd heapBase 64`). No fuel premise. |
| `16db278ae` | `HeaderWithdrawalLoopWhile` | `wd_slice_args` (encoder argument `X + (I0 + ofNat k) * 44` read from `memory (pl + 48)`), `wdSliceInv`, and **`wdSliceLoop_window`**: the signed slice loop preserves the watched cell at every fuel. |
| `7fc4d55f8` | `HeaderWithdrawalStatement46` | `payloadHeader46_window`: composition through `source_wd_slice_loop` + the `seq` split, with the statement 47 tail as an explicit hypothesis. |
| `fb861ac3b` | `HeaderWithdrawalLoopWhile` | `noControl` **discharged from source semantics**: `not_control_of_control`, `assign_local_control`, `wdSliceLoopStores_control`, `decCall_noControl`, `wdSliceLoopBody_noControl`. The `noControl` hypothesis was removed from `wdSliceLoop_window` and `payloadHeader46_window`. |
| `c31e808e1` | `HeaderWithdrawalEntryFacts` | concrete heap chain `wdHeapWord heapBase j = heapBase + ofNat 64 (64 * j)` with `wdHeapWord_zero`, `wdHeapWord_toNat`, `wdHeapWord_succ` (through `allocationEnd_aligned_exact`), `wdHeapWord_bounds`, `wdHeapWord_out`; and **`payloadHeader46_window_entry`**: statement 46 on concrete entry facts only. |

Module import order (replay in this order after a clean `.olean` dir):

```
InitECandidate.Runtime.RlpWithdrawalGlobalsFuel
InitECandidate.Runtime.HeaderWithdrawalLoopBody          -- imports HeaderWithdrawalLoopFrame, PanSingleWordLookup
InitECandidate.Runtime.HeaderWithdrawalLoopWhile         -- imports HeaderWithdrawalLoopBody, MptReadFrame
InitECandidate.Runtime.HeaderWithdrawalStatement46       -- imports HeaderWithdrawalLoopWhile
InitECandidate.Runtime.HeaderWithdrawalEntryFacts        -- imports HeaderWithdrawalStatement46, RlpWindowShiftGeneral, Bn254AccelInitSource
```

## What is proved

1. **The loop invariant is signed and fuel-free.** `wdSliceInv t I0 nwd pl slices w read H s` is
   `∃ k, I0.toNat + k ≤ nwd.toNat ∧ …`: counter `i = I0 + ofNat 64 k`, `nwd`/`pl` fixed, `e` erased,
   `wd_rlp_slices` fixed, `heap_ptr = H k`, `code = originalRuntimeCode`, `memaddrs read`, and both
   watched cells (`w` and `read = pl + 48`) still equal to their entry values. There is **no**
   `3 ≤ s.clock` premise and no fuel: on the `none` outcome the successor invariant is derived from
   the actual normal encoder/alloc/call run (`wd_slice_step_successor`); at `clock = 0` the `decCall`
   times out (`evaluateHOLFiniteState_decCall_clock_zero`) and no successor invariant is needed.
   The `Cmp.less` condition is the HOL signed comparison, so the entry `k+1` bound is obtained from
   `cond_less_small` plus the real count/allocation facts (`toNat` of `I0 + ofNat k`), never by
   assuming an unsigned rank.
2. **`noControl` is a theorem, not an assumption.** `wdSliceLoopBody_noControl s` holds for every
   state: `(evaluateHOLFiniteState s wdSliceLoopBody).1` is never `some .continue` or `some .break`.
   It is proved from the actual source: the body is a `decCall` whose continuation is the three
   stores (`wdSliceLoopStores`), and `wdSliceLoopStores_control` shows those only complete (`none`)
   or fail (`some .error`) — `evaluate_store_control_frame` for the two stores,
   `assign_local_control` (from `evaluateHOLFiniteState_assign`) for the counter increment; the
   `decCall` cases then give `none`/`error`/`timeOut`/`returned` and the continuation's own result,
   all of which `not_control_of_control` excludes.
3. **The per-iteration window is fuel-free** (`wd_slice_step_window`): the alloc call writes only
   inside the 64-byte block at `H k`, and both watched cells are outside it (`outW`/`outR` + slice
   disjointness), so `memory w` and `memory read` survive the iteration.
4. **The heap chain is derived, not assumed** (`HeaderWithdrawalEntryFacts`): with the arena 8-aligned
   and inside the allocator limit, `H (j+1) = allocationEnd (H j) 64` and the in-range bounds hold;
   a single `¬ MWin heapBase (64 * nwd.toNat + 64) w` yields every per-iteration window through
   `mwin_shift_nat`/`mwin_mono`.

## Exact remaining entry facts (for root at the statement 46 boundary)

`payloadHeader46_window_entry` consumes exactly these, all at the statement 46 entry state `t`:

- `readEq : read = pl + 48#64` — the slice record the encoder is handed;
- counter/locals: `t.locals "i" = word I0`, `t.locals "nwd" = word nwd`, `t.locals "pl" = word pl`,
  `t.locals "e" = none` (the `e` local is erased before the loop);
- globals: `t.globals "wd_rlp_slices" = word slices`, `t.globals "heap_ptr" = word heapBase`;
- `code : t.code = originalRuntimeCode`;
- arena/limit: `heapBase.toNat % 8 = 0`, `heapBase.toNat + 64 * nwd.toNat + 128 < 2^64`,
  `heapBase.toNat + 64 * nwd.toNat + 64 ≤ 33806089496`;
- count: `I0.toNat ≤ nwd.toNat`, `nwd.toNat < 2^63`;
- watched cells outside the whole run: `¬ MWin heapBase (64 * nwd.toNat + 64) w`,
  `¬ MWin heapBase (64 * nwd.toNat + 64) read` (the concrete window lemmas `mwin_below`,
  `mwin_above`, `mwin_off` are available to derive these from the real address geometry);
- `t.memaddrs read`, `t.memory read = HolWordLab.word X` (the first slice record’s first word);
- slice disjointness for every iteration `j ≤ nwd.toNat`:
  `w` and `read` differ from `slices + (I0 + ofNat 64 j) * 16#64` and from that `+ 8#64`;
- statement 47 tail (root-owned):
  `(evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2 (actualPayloadHeaderAt 47)).2.memory w
     = (evaluateHOLFiniteState t wdSliceLoop).2.memory w`.

Nothing else is assumed. In particular there is no fuel/clock premise, and no `noControl` input.

## Replay

```bash
cd work/finite-flash-work
rm -f lib/lean/InitECandidate/Runtime/{RlpWithdrawalGlobalsFuel,HeaderWithdrawalLoopBody,HeaderWithdrawalLoopWhile,HeaderWithdrawalStatement46,HeaderWithdrawalEntryFacts}.olean
for m in RlpWithdrawalGlobalsFuel HeaderWithdrawalLoopBody HeaderWithdrawalLoopWhile \
         HeaderWithdrawalStatement46 HeaderWithdrawalEntryFacts; do ./pcheck.sh Runtime.$m; done
# expect: OK … and AXIOMS … [propext, Classical.choice, Quot.sound] for each
```

Statements 47/48/49 are untouched by this work.
