# Statement 46 — remaining work (after `8d4d7371b`)

## Green so far (checked, axioms clean)
- `wd_slice_stores_window` — one iteration preserves `memory w` (stores + heap-window + apartness).
- `cond_less_small` — signed `Cmp.less` on `i`/`nwd` reduces to `Nat` comparison when both are
  `< 2^63`.
- `wdSliceLoopStores_adv` — `AdvStep "i" 1 wdSliceLoopStores` (`.word/.word/.advance`).
- `wd_slice_stores_globals_frame` — `OriginalGlobalsFrame wdSliceLoopStores` (leaf/store/assign).
- `wd_slice_step_successor` — on the normal path of one iteration:
  `locals "i" = I + 1`, `locals "nwd"/"pl"` fixed, `locals "e" = none`,
  `globals "wd_rlp_slices"` fixed, `globals "heap_ptr" = allocationEnd heapBase 64`.
  Proof shape: `evaluateHOLFiniteState_decCall_total` + `pan_single_word_lookup_shape` +
  `rw [if_neg (by omega)]` + `rw [bodyRun]` + `dsimp only [fixClockHOLFinite]` +
  `simp only [shapeOk,Bool.and_self,if_true,ite_true]` + `rw [← contStateDef]; rw [stepRun]`
  to get **one** `bodyEq : eval t wdSliceLoopBody = (result, {advanced with locals := resVarEq advanced.locals entryPair})`;
  then `rw [bodyEq] at hnormal` gives `result = none`, and the six conjuncts follow from
  `hi`/`frame`/`globalsKept` + `lookup_resVarEq_none,FDOMSUB_HOL`.
  NOTE: the continuation-state clock is `if entry.clock < st.clock then entry.clock else st.clock`
  (entry = `callEntryStateHOLFinite …`), *not* `t.clock` — `set contState` must spell it out.

## Remaining: the signed while invariant
Apply `MptReadFrame.evaluate_while_watch` with
```
Inv s := ∃ (I H : BitVec 64),
  s.locals.lookup "i" = some (.val (.word I)) ∧
  s.locals.lookup "nwd" = some (.val (.word nwd)) ∧
  s.locals.lookup "pl" = some (.val (.word pl)) ∧
  s.locals.lookup "e" = none ∧
  s.globals.lookup "wd_rlp_slices" = some (.val (.word slices)) ∧
  s.globals.lookup "heap_ptr" = some (.val (.word H)) ∧
  s.code = originalRuntimeCode ∧
  s.memory w = t.memory w ∧ s.memory (pl + 48#64) = t.memory (pl + 48#64) ∧
  I.toNat ≤ nwd.toNat ∧ I.toNat < 2^63 ∧ (* rank *) H = heapBase + ofNat 64 (64 * (I.toNat - I0.toNat)) ∧
  ¬ MWin H (64 * (nwd.toNat - I.toNat + 1)) w ∧
  ¬ MWin H (64 * (nwd.toNat - I.toNat + 1)) (pl + 48#64)
```
Deliverables for the step obligation:
1. `memory w` / `memory (pl+48)` preserved: `wd_slice_step_window` twice (second instance with
   cell `pl+48`; needs `pl+48 ≠ slices + I*16` and `≠ slices + I*16 + 8` — static hypotheses of the
   loop lemma, `∀ j ≤ nwd, …`), at state `decClockHOLFinite s` (clock/locals/globals/memory same).
2. Successor facts: `wd_slice_step_successor` (needs `normal` from the step's `none` outcome) —
   but note the loop's step obligation is also given `continue`/`break` outcomes; the stores cannot
   produce them (`store`/`assign` yield `none` or `error` only), so close those branches by
   contradiction: the body is `decCall` whose only non-`none` outcomes are `error`/other results,
   so `none` is forced by `decCall_total`'s shape only in the returned branch → use the same
   unfolding as in `wd_slice_step_successor` to show the result is `some _` in those branches.
3. Heap arithmetic: `allocationEnd H 64 = H + 64` from 8-alignment (`H = heapBase + 64k` gives
   alignment; `allocationEnd_eq_align` + `BitVec` `and`-with-mask reduction), and the budget
   window shrinks: `¬MWin H (64*(r+1)) w → ¬MWin (H+64) (64*r) w`
   (`MWin (H+64) (64*r) w → MWin H (64 + 64*r) w` via the shift lemma
   `mwin_shift_nat`/`mwin_narrow_shift` family in `RlpWindowShiftGeneral`; monotonicity
   `mwin_mono` since `64 + 64*r ≤ 64*(r+1)`).
4. Exit: `I.toNat = nwd.toNat` from `¬(I.toNat < nwd.toNat)`; the loop's `v ≠ 0` hypothesis plus
   `cond_less_small` gives `I.toNat < nwd.toNat` on entry to the body.

## Then
Compose with `source_wd_slice_loop : actualPayloadHeaderAt 46 = .seq wdSliceLoop (actualPayloadHeaderAt 47)`
(after the `evaluateHOLFiniteState_seq_line780` step) to hand statement 47 its starting state.

## Update after `5ea2f9da2`
Green additionally: `wd_slice_step_outcome` — a *normal* iteration forces the encoder to return
`.rStruct [.val (.word first), .val (.word second)]` with a true `.comb [.one,.one]` shape check
(`cases bodyRun` + `cases hshape : shapeEqHOL … Bool`; in the `true` branch the run equation in the
goal is already `rfl`, the returned witnesses are `⟨first,second,st,rfl,hshape⟩`).
So the loop step never needs `bodyRun` as a hypothesis: `wd_slice_step_outcome` + `wd_slice_step_successor`.

### Fuel: do NOT prove clock positivity inside the loop
`wd_slice_step_window` needs `3 ≤ t.clock` only to feed `rlpEncodeWithdrawal_other_globals`'s
`2 ≤ entry.clock`. The clock cannot be re-proved per iteration, so pass it as a *premise of the loop
lemma*:
```
theorem wdSliceLoop_window … (Inv : state → Prop) (inv0 : Inv t)
    (fuel : ∀ s, Inv s → 3 ≤ s.clock) : (eval t wdSliceLoop).2.memory w = t.memory w
```
`evaluate_while_watch`'s step then gets `3 ≤ s.clock` from `fuel s (inv s)` and nothing else about fuel.
`rlpEncodeWithdrawal_window` itself is already fuel-free (`RlpWithdrawalWriter.lean:1012`).

### Invariant (per-cell; apply once for `w` and once for `read := pl + 48#64`)
```
Inv s := ∃ k : Nat, k ≤ nwd.toNat ∧
  s.locals "i" = some (.val (.word (I0 + BitVec.ofNat 64 k))) ∧
  s.locals "nwd" = some (.val (.word nwd)) ∧ s.locals "pl" = some (.val (.word pl)) ∧
  s.locals "e" = none ∧ s.globals "wd_rlp_slices" = some (.val (.word slices)) ∧
  s.globals "heap_ptr" = some (.val (.word (H k))) ∧ s.code = originalRuntimeCode ∧
  s.memory w = t.memory w ∧ s.memory read = t.memory read
```
with the static facts (conjuncts of the loop lemma, kept through the invariant as `∀ j` premises):
* `H 0 = heapBase`, `∀ j, H (j+1) = allocationEnd (H j) 64`,
  `∀ j ≤ nwd, ¬ MWin (H j) 64 w`, `∀ j ≤ nwd, ¬ MWin (H j) 64 read`,
  `∀ j ≤ nwd, (H j).toNat + 71 < 2^64`  (feeds `heapBound`);
* `∀ j ≤ nwd.toNat, w ≠ slices + (I0 + ofNat j) * 16 ∧ w ≠ slices + (I0 + ofNat j) * 16 + 8`
  (same for `read`) — these discharge `slice0/slice8`;
* `t.memory (pl + 48#64) = .val (.word X)` for a fixed word `X`: the argument at iteration `k` is
  `X + (I0 + ofNat k) * 44`, so `hargs` is *derived* each iteration by `simp` from
  `locals "pl"`, `locals "i"` and `memory (pl+48)` — no `hargs` in the invariant.

Step outline (given `Inv s` and the condition word `v ≠ 0`):
1. `fun`-intro; `entered := decClockHOLFinite s`; lookups transfer by `simp [decClockHOLFinite]`.
2. `hargs` by `rw [evalListHOLFinite_eq_toExact]; simp [...]` (KeccakMainLoopWindow:30 is the pattern).
3. `cond_less_small` gives `¬(I.toNat < nwd.toNat) → …`; with `v ≠ 0` it gives `I.toNat < nwd.toNat`,
   hence `k < nwd.toNat` and so `k+1 ≤ nwd.toNat` for the successor index.
4. `wd_slice_step_window` for `w`, again for `read` → both memory facts at `entered`.
5. `wd_slice_step_outcome` (needs `3 ≤ entered.clock` from `fuel` and `hargs`) then
   `wd_slice_step_successor` → `i = I+1`, `nwd/pl/e/slices` fixed,
   `heap_ptr = allocationEnd (H k) 64 = H (k+1)`; conclude `Inv post` with `k+1`.
6. `evaluate_while_watch … |> .1`, then compose with `source_wd_slice_loop` and
   `evaluateHOLFiniteState_seq_line780` for statement 47's starting state.
