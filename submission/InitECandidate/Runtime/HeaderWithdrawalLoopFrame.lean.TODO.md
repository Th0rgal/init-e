# Statement 46 (withdrawal slice loop): state of play

## Checked green (commit of this note)

`HeaderWithdrawalLoopFrame.lean`, axioms `propext, Classical.choice, Quot.sound`:

* `wdSliceLoopCondition`, `wdSliceLoopStores`, `wdSliceLoopBody`, `wdSliceLoop` —
  the concrete loop of statement 46 (mirrored literally from the guest AST:
  condition `i < nwd` uses `Cmp.less`, not `Cmp.lower`; the encoder argument is
  `load [pl + 48] + i*44`; the two stores are `wd_rlp_slices + i*16` and
  `+ i*16 + 8` storing `e.0` and `e.1`; then `i := i + 1`).
* `source_wd_slice_loop : actualPayloadHeaderAt 46 = .seq wdSliceLoop (actualPayloadHeaderAt 47)`.
* `valueWords_of_comb` — a value whose shape is `.comb [.one,.one]` is exactly
  `.rStruct [.val (.word first), .val (.word second)]`; this is how both slice
  stores get their words from the *actual* returned tuple.
* `PayloadHeaderTailSources.source_actual_payload_header_withdrawal_loop` now
  states the whole loop concretely (previously only `∃ loop, … = .seq loop …`).

## Next: the per-iteration and loop statements

Per iteration (`wdSliceLoopBody`), with `heapBase` the `heap_ptr` global at the
iteration start and `cell` the watched word:

1. `evalListHOLFinite` of `[.op .add [load [pl+48], panop mul [i, 44]]]` gives
   `[.val (.word (inputWord + counter * 44))]` where `t.memory (pl + 48) = .word inputWord`.
2. `pan_single_word_lookup` on the frozen `encode_withdrawal_rlp` lookup gives
   the callee `{pl ↦ arg}` and return shape `.comb [.one,.one]`.
3. `decCall_window` composes: `hbody` = `rlpEncodeWithdrawal_window entry heapBase W cell …`
   (needs `¬ MWin heapBase 64 cell`, `heapBase.toNat + 64 < 2^64`), and `hcont`
   is the two-store chain, whose value is `valueWords_of_comb hshape`.
4. The two-store chain: use `evaluate_wordStore_memory_frame`
   (`StoreControlFrame.lean`/`BoundWordStoreChainFrame.lean` pattern) twice plus
   the `i := i + 1` assign (`readOnlyMemory = true`).
   Note: `BoundWordStoreChainFrame` binds only *locals*, so its `target` goal
   cannot see `t.globals`; the addresses depend on the global `wd_rlp_slices`.
   Either add a `globals`-pinned variant of the frame, or do the three steps by
   hand with `evaluate_wordStore_memory_frame` + `evaluate_store_control_frame`
   (which gives `result = none ∨ result = error`, `.locals` and `.clock`;
   globals are preserved because the store result is `{state with memory := …}`,
   so a one-line `store_globals` lemma by `rw [evaluateHOLFiniteState_store] <;> split <;> rfl`
   is enough for the intermediate states).
5. Allocation/read/rejection outcomes: the encoder call can fail (allocation
   rejection inside `alloc`, or a failed byte read) — then the decCall's result
   is `.error`/`.timeOut` and, by `rlpEncodeWithdrawal_window`, the watched cell
   is still unchanged; the two stores are never reached.
6. The loop itself: `evaluateHOLFiniteState_while_total` plus an invariant
   `¬ MWin heapStart (64 * nwd) cell ∧ cell ∉ {wd_rlp_slices + k*16, +8}`,
   with `mwin_mono`/`mwin_narrow_shift` moving the heap window each iteration
   (`heap_ptr` grows by 64 per iteration, `i` by one).

Target end shape (model `HeaderWithdrawalsBytesStateRoot.lean`):

    Reaches s (actualPayloadHeaderAt 46)
      (fun post => post.memory (record + 32#64) = .word word ∧ frame …)
      cost (actualPayloadHeaderAt 47)

Not touched by me: statements 47/48/49 (root owns them).
