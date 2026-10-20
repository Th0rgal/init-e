# Statement-46 loop: state of the proof (after e50a893ec)

GREEN and committed, axioms `propext, Classical.choice, Quot.sound` only:

* `RlpWithdrawalGlobals` — globals frames for all nine writer callees + call-step wrappers.
* `RlpWithdrawalHeap.rlpEncodeWithdrawal_returned_globals` — a returned encoder run changes exactly
  one global: `base.globals = (setGlobalHOLFinite "heap_ptr" (.val (.word (allocationEnd B 64))) t).globals`;
  corollaries `rlpEncodeWithdrawal_heap` and `rlpEncodeWithdrawal_other_globals`.
* `HeaderWithdrawalLoopStep.wd_slice_stores_window` — the two slice stores plus increment keep every
  other cell, for every store outcome.
* `PanSingleWordLookup.pan_single_word_lookup_shape` — generic single-word call lookup (any return
  shape); see the recipe below.
* `HeaderWithdrawalLoopBody.wd_slice_step_window` — the full per-iteration composition: encoder window
  (hbody), and the continuation with `baseSlices`/`baseMemory` transfers, `wd_slice_stores_window` at
  `setVarHOLFinite "e" <returned tuple> {base with clock := k, locals := t.locals}`, then `rw [stores]`.
* `HeaderWithdrawalLoopBody.cond_less_small` — the loop condition `i < nwd` is the *signed*
  `holAsmSignedLess`, and below `2^63` it is exactly `i.toNat < nwd.toNat`
  (via `CountedLoop.holAsmSignedLess_small`), with the `v ≠ 0 ↔` equivalence.

## What is left for statement 46

1. **Successor-state facts for one iteration** (the missing piece): given the hypotheses of
   `wd_slice_step_window`, the post-state of `wdSliceLoopBody` satisfies
   `locals "i" = some (.val (.word (I + 1)))`, `globals "heap_ptr" = some (.val (.word (allocationEnd heapBase 64)))`,
   `globals "wd_rlp_slices"` and `locals "nwd"`/`"pl"` unchanged, `code` unchanged.  This is a
   `decCall_returned_globalsG`-style decomposition of the body *plus* `evaluate_store_control_frame`
   for the two stores and the increment — mirror `RlpWithdrawalHeap.rlpEncodeWithdrawal_heap`'s
   structure for the globals and `StoreLoopWindow.evaluate_advStep` for the counter.
2. **While induction**: `MptReadFrame.evaluate_while_watch` with
   `Inv s := ∃ I heapBase, <the hypotheses of `wd_slice_step_window` at s> ∧ s.memory w = t.memory w ∧
   I.toNat ≤ nwd.toNat ∧ I.toNat < 2^63`, step obligation from `wd_slice_step_window` + (1); the
   condition value is supplied as a hypothesis, so `cond_less_small` is only needed to justify that the
   loop actually *exits* (`i = nwd`), not for the window conclusion.
3. **Statement 46 closure**: `source_wd_slice_loop : actualPayloadHeaderAt 46 = .seq wdSliceLoop
   (actualPayloadHeaderAt 47)`, so the statement-46 fact is the loop window lemma composed with the
   root-owned statement 47.

## Recipe that worked for the generic lookup (kept for the record)

`unfold lookupCodeHOLFinite; split` (a plain `rw` under the dependent `match h :` fails with "motive is
not type correct"), then in the `some` branch `rw [raw] at found`, two `Prod.mk.inj (Option.some.inj
found.symm)`, `subst` the equalities, then `congrArg (fun locals => some (foundBody,locals,foundShape))`
+ `HolFiniteMapExact.ext` + `funext` + `simp [...]` with the `key = parameter` split.  And for the
`setVarHOLFinite` lookup: `change` to the concrete state, `simp only [setVarHOLFinite,
HolFiniteMapExact.lookup_update, FUPDATE]`, then `rw [if_pos (show (ofString "e" == ofString "e") =
true by decide)]` — `if_pos rfl` does *not* fire because the test is a `BEq` comparison.
