# Statement-46 per-iteration lemma: remaining obstacle

Checked green so far (commits `3a2f8e6ba`, `b0f2c74bf`, `6026fb11d`, plus the stores lemma):

* `RlpWithdrawalHeap`: `rlpEncodeWithdrawal_returned_globals` — a *returned* encoder run satisfies
  `base.globals = (setGlobalHOLFinite "heap_ptr" (.val (.word (allocationEnd B 64))) t).globals`,
  and the two corollaries `rlpEncodeWithdrawal_heap` (heap pointer advances to
  `allocationEnd B 64`) and `rlpEncodeWithdrawal_other_globals` (every other global, in
  particular `wd_rlp_slices`, is untouched).  Derived from the real `alloc` body and the nine
  writer-callee globals frames, not assumed.
* `HeaderWithdrawalLoopStep.wd_slice_stores_window` — one iteration's two slice stores (words taken
  from the returned two-word tuple via `valueWords_of_comb`) plus the counter increment keep every
  cell outside `slices + i*16` and `slices + i*16 + 8`, for every store outcome.
* `HeaderWithdrawalLoopBody.wd_slice_step_window` — the intended composition of
  `decCall_window` with `rlpEncodeWithdrawal_window` (body), the stores lemma (continuation),
  `valueWords_of_comb` and `rlpEncodeWithdrawal_other_globals` (slice pointer in the continuation).

## RESOLVED: generic single-word lookup

`PanSingleWordLookup.pan_single_word_lookup_shape` is now GREEN (same axioms): the trick is
`unfold lookupCodeHOLFinite; split` (a plain `rw` under the dependent `match h :` fails with
"motive is not type correct"), then in the `some` branch `rw [raw] at found`,
`Prod.mk.inj (Option.some.inj found.symm)` twice, `subst` the three equalities, and only then
`congrArg (fun locals => some (foundBody,locals,foundShape))` +
`apply HolFiniteMapExact.ext; funext key; simp [HolFiniteMapExact.lookup_update,FUPDATE,
HolFiniteMapExact.empty,FEMPTY]` with the `key = parameter` case split.  Do not try to rewrite a
raw function into the finite map.

## Remaining obstacle in `wd_slice_step_window` (draft, `.disabled`)

`pan_single_word_lookup` (PanSingleWordLookup.lean) only handles a callee whose declared return
shape is `.one`; the withdrawal encoder declares `.comb [.one,.one]`.  The generalization

    theorem pan_single_word_lookup_shape ... (returnShape : ShapeHOL)
        (lookup : code name = some ([(parameter,.one)],body,returnShape)) :
        lookupCodeHOLFinite code name [.val (.word amount)] =
          some (body, HolFiniteMapExact.empty.update (parameter, .val (.word amount)), returnShape)

was what `wd_slice_step_window` needed; it is solved.  The draft now compiles its body/argument
part and fails only in the continuation's record hypothesis:

    atRecord : (setVarHOLFinite "e" (.rStruct [.val(.word first),.val(.word second)])
                  {base with clock := k, locals := t.locals}).locals.lookup "e" = some (...)

`simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]` there reduces the left-hand side
to the *else* branch `t.locals.lookup "e"` instead of returning the bound value, i.e. the
`if key = name` test is not discharged by the simp set as used in the `?_` placeholder.  Fix
route: state `HolFiniteMapExact.lookup_update`'s `if_pos` explicitly (the exact formulation is in
`.lake/packages/flapjack/Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean`), or prove the
hypothesis with `show` on the concrete state and `rw [HolFiniteMapExact.lookup_update,
if_pos (by simp)]`.  Everything else is in place: entryHeap/entryWd/entryCode/entryClock,
`baseSlices` via `rlpEncodeWithdrawal_other_globals`, `baseMemory` via
`rlpEncodeWithdrawal_window` (so the continuation state's memory equals `t.memory`), then
`wd_slice_stores_window` at `{base with clock := k, locals := t.locals}` and `rw [stores]`.

The earlier failure description retained for context: the old version failed only in its final step: after
`rename_i foundBody foundLocals foundShape found` and `obtain ⟨rfl,rest⟩ := Prod.mk.inj equal`,
`obtain ⟨localsEq,shapeEq⟩ := Prod.mk.inj rest`, the local `foundLocals` has type
`MlS → Option (ValueHOL width)` (a *function*) while the goal wants the `HolFiniteMapExact`
structure, so both `rw [localsEq]` and `HolFiniteMapExact.lookup` fail:
"motive is not type correct" / "Invalid field `lookup`".  Note the original `.one` version succeeds
because it never rewrites the locals component — it only rebuilds the literal with
`congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))` and then extends *that*
existing function equality.  The fix is to make the generalized lemma's `raw` step produce the
structure directly (i.e. state `raw` about `lookupCodeHOLFinite` instead of `lookupCodeHOLExact`,
or wrap the function in `HolFiniteMapExact.mk` with its finite support proof) so that
`Prod.mk.inj` yields a structure equality that `congrArg` can consume; then `subst shapeEq` for
the return shape.

Everything else in `wd_slice_step_window` (encoder window from `rlpEncodeWithdrawal_window`,
`callEntryStateHOLFinite` heap/`wd`/code transfer, slice pointer through
`rlpEncodeWithdrawal_other_globals`, and the three continuation-side lookups with
`setVarHOLFinite`) is already written down in this handoff's sibling attempt.

## After that

* discharge `hargs` (the `load [pl+48] + i*44` argument) from `panMemLoadHOL` facts;
* signed `Cmp.less` smallness of `i`/`nwd` (`toNat < 2^63`) from the real count invariant;
* the `while` induction over `wdSliceLoop` with `mwin_mono`/`mwin_narrow_shift`, then statement 46
  closes with `source_wd_slice_loop`.
