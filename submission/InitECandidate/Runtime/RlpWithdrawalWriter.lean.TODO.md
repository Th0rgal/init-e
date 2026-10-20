# encode_withdrawal_rlp window: COMPLETE

`rlpEncodeWithdrawal_window` is proved: writing one withdrawal record touches
no cell outside the freshly allocated 64-byte buffer at the heap pointer.  The
allocatory step reuses the existing `alloc_memKeep` (`AccountLeafAnyAlloc`) and
`alloc_body_returned` (`HtabGrowRehash`), so no new allocation theory was needed.

## History

## Checked green (`pcheck.sh Runtime.RlpWithdrawalWriter`, axioms
`propext, Classical.choice, Quot.sound`, no `sorry`)

Every lemma has the shape `(eval t SUFFIX).2.memory w = t.memory w` under
`¬ MWin B 64 w`, `B.toNat + 64 < 2^64`, `p = B + ofNat K` with the tight offset
budget, locals `buf ↦ B`, `p ↦ P`, `wd ↦ W`, `code = originalRuntimeCode`:

* `wdFinishTail_window` — `p += w`, `rlp_finish_list`, `return {buf,total}`.
* `wdCall36_window` — amount word call + tail (`K ≤ 48`).
* `wdCallBytes_window` — 20-byte address field + tail (`K ≤ 27`).
* `wdCall8_window` — second record word + tail (`K ≤ 18`).
* `wdAssign8_window` — offset advance + tail (`K ≤ 9`, returned word `H.toNat ≤ 9`).
* `wdCall0_window` — first record word via the destructuring `decCall`.
* `wdDecP_window` — `p := buf + 9` + entire writer chain.

Record-word arguments stay abstract: a failed load makes the call `.error`
(memory untouched) and a successful load's shape check makes the value a word
(`rlpEncodeWord_second_word`), so no record-read hypotheses are needed.

## New module in progress: `AllocationMemoryFrame.lean`

Goal: `(eval entry (sourceFunctionBody Guest.guestFn_alloc)).2.memory w
= entry.memory w`, i.e. `MemoryFrame (sourceFunctionBody Guest.guestFn_alloc)`.

Reusable machinery already in the tree:

* `MemoryFrame program` (HtabSetBound.lean) = memory *and* globals preserved in
  every outcome under `code = originalRuntimeCode`; combinators
  `memoryFrame_leaf` (via `readOnlyMemory program = true`),
  `memoryFrame_seq`, `memoryFrame_dec`, `memoryFrame_ite`, `memoryFrame_decCall`.
* `readOnlyMemory` (ReadOnlyMemory.lean) is *syntactic* and returns `false` for
  `.call`, so the allocator body (which contains
  `.call (some (none,none)) "trap_with" [.const 1]`) is not syntactically
  read-only.
* `evaluate_decCall_readOnly_frame` (PanDecCallReadFrame.lean) already proves the
  left-outcome frame for a `.decCall` whose callee body is read-only — the model
  to copy. There is **no** plain-`.call` analogue yet.
* `alloc_body_returned` (HtabGrowRehash.lean) and `evaluate_source_alloc_success`
  (AllocationSuccess.lean) give `post.memory = state.memory` for the returned
  (`some (.returned …)`) outcome only.

## Next actions (in order)

1. `evaluate_call_readOnly_frame` in `AllocationMemoryFrame.lean`: for a plain
   `.call` node, given `args : evalListHOLFinite … = some values`,
   `lookup : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape)`
   and `readOnlyMemory body = true`, conclude
   `(eval state (.call …)).2.memory = state.memory`
   (and globals). Mirror `evaluate_decCall_readOnly_frame` using the
   `evaluateHOLFiniteState_call_args_none / _lookup_none / _clock_zero /
   _body_error / _body_break / _body_continue / _return_none /
   _return_shape_mismatch / _return_caller_locals` lemmas in
   `.lake/packages/flapjack/.../EvaluateSem/../EvaluateClock.lean`.
2. `readOnlyMemory` of the `trap_with` body (via its source body equation and
   `rfl`), so step 1 applies to the allocator's trap guard.
3. `alloc_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_alloc)` by
   `rw [source_alloc_body]` then `memoryFrame_dec` + `memoryFrame_seq` +
   `memoryFrame_ite` over the trap call (steps 1–2) and the read-only `.skip` /
   `.dec "q" … allocationFinish` remainder.
4. Top level, in `RlpWithdrawalWriter.lean`:

       theorem rlpEncodeWithdrawal_window {F} (t) (B W w) (heap : t.globals.lookup "heap_ptr" = some (.val (.word B)))
         (hwd : t.locals.lookup "wd" = some (.val (.word W)))
         (out : ¬ MWin B 64 w) (hB : B.toNat + 64 < 2^64) (code : t.code = originalRuntimeCode) :
         (eval t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)).2.memory w = t.memory w

   Proof: `source_rlpEncodeWithdrawal_body`, `evaluateHOLFiniteState_decCall_total`
   with `evalListHOLFinite [.const (64#64)] = some [.val (.word (64#64))]`, exact
   allocation lookup (`originalRuntimeCode_allocation_lookup` +
   `lookupCodeHOLFinite_of_exact`), then `decCall_window` with
   `hbody := alloc_memoryFrame …`, and `hcont` = the `wdDecP_window` level after
   `setVarHOLFinite "buf" (.val (.word state.globals "heap_ptr")) {base with clock := k, locals := t.locals}`
   (the decoder's `buf` local becomes the allocator's returned pointer, so
   `hb : buf ↦ B` comes from the returned-value equation of `alloc_body_returned`).

## After the withdrawal statement

Next task: header slices, statement 46 (`wd_rlp_slices + i * 16` stores).
