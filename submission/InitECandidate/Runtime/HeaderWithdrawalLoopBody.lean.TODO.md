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

## The single missing piece

`pan_single_word_lookup` (PanSingleWordLookup.lean) only handles a callee whose declared return
shape is `.one`; the withdrawal encoder declares `.comb [.one,.one]`.  The generalization

    theorem pan_single_word_lookup_shape ... (returnShape : ShapeHOL)
        (lookup : code name = some ([(parameter,.one)],body,returnShape)) :
        lookupCodeHOLFinite code name [.val (.word amount)] =
          some (body, HolFiniteMapExact.empty.update (parameter, .val (.word amount)), returnShape)

is what `wd_slice_step_window` needs, and it fails only in its final step: after
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
