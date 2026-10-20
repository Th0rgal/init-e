# Heap advancement of `encode_withdrawal_rlp` (statement-46 prerequisite)

Goal (lead: "actual encoder returned heap advancement, not an assumed +64"):

    (evaluateHOLFiniteState t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)
       = (some (.returned value), base)) →
    base.globals.lookup "heap_ptr" = some (.val (.word (allocationEnd B 64)))

with `t.globals.lookup "heap_ptr" = some (.val (.word B))`, `t.code = originalRuntimeCode`,
`2 ≤ t.clock`.  With `allocationEnd B 64 = B + 64` for 8-aligned `B`
(`AllocationRound.allocationEnd_eq_align`) this is the real (+64) advancement: it moves the
window each iteration with `mwin_mono`/`mwin_narrow_shift` while cells below the initial heap
stay protected.

## Checked already (green, committed `6b5d0f889`)

`RlpWithdrawalGlobals.lean`, axioms `propext, Classical.choice, Quot.sound`:

* `originalGlobalsFrame_tail_call` — `.call none`, installed body frame ⇒ globals frame;
* `originalGlobalsFrame_local_call` — `.call (some ((some (.local,n)),none))`;
* `originalGlobalsFrame_local_decCall` — declaration call + continuation frame.

## Missing pieces, in order

1. Callee body globals frames (all nine, by structural composition of the `source_*_body`
   equations; the recursion closes):
   * leaves (`originalGlobalsFrame_leaf _ (by intro watched; rfl)`): `rlp_be_len`,
     `rlp_put_be`;
   * `rlp_header_len` ← `rlp_be_len`; `rlp_write_header` ← `rlp_be_len` + `rlp_put_be`;
     `rlp_encode_list_header` ← `rlp_write_header`; `rlp_encode_bytes` ← `rlp_write_header`
     + `memcpy` (`memcpy_body_globals_frame` exists); `rlp_finish_list` ← `memcpy` +
     `rlp_encode_list_header` + `rlp_list_header_len`; `rlp_encode_word` ← `rlp_be_len` +
     `rlp_put_be`.
   * call nodes: `originalGlobalsFrame_discard_call` (`memcpy`, `rlp_put_be`,
     `rlp_encode_list_header`; lookups in `OriginalRlpWriterCode` / `OriginalMemcpyCode`),
     `originalGlobalsFrame_local_decCall` (`"ll"`, `"h"`, `"hl"`).
   * **Tactic trap** (cost cycles): with a composite continuation,
     `exact originalGlobalsFrame_local_decCall _ _ _ _ _ _ lookup frame _ contFrame _`
     does not infer `name`/`shape`/`arguments` and reports a bogus
     "expected ShapeHOL / expected ProgHOL".  Working recipe: first bind the continuation
     frame with its explicit type
     (`have tail : OriginalGlobalsFrame (<literal continuation>) := <composition>`), then
     pass `(name := …) (shape := .one) (arguments := [...])` plus explicit
     `parameters`/`body`/`returnShape` placeholders, or add a thin wrapper lemma with those
     three implicit.
2. Writer tail frames over `RlpWithdrawalWriter` defs: `wdFinishTail`, `wdCall36`,
   `wdCall36Tail`, `wdCallBytes`, `wdCallBytesTail`, `wdCall8`, `wdCall8Tail`,
   `wdCall0` (a `decCall` binding `w`), `wdCall0Tail`, `wdDecP` (`.dec "p"`), each
   `OriginalGlobalsFrame`; `wdAssign` is an `.assign .local` leaf.
   Mind the exact associativity: `wdCallBytesTail = .seq wdAssign (.seq wdCallBytes
   wdCallBytesTail)` (a `.seq (.seq …) …` re-association is a type mismatch).
3. The heap theorem: `rw [source_rlpEncodeWithdrawal_body, rlpEncodeWithdrawal_eq] at run`;
   split the `alloc` call with `decCall_returned_globalsG` (HtabGrowTop — the variant that
   carries `post.globals = inner.globals`); pin the lookup with
   `originalRuntimeCode_allocation_lookup` + `pan_single_word_lookup` (size `64`);
   `alloc_body_returned` gives `bodyPost.globals = setGlobal "heap_ptr"
   (.val (.word (allocationEnd B 64)))` (**8** conjuncts: `request, finish, hw, bm, ba, bb,
   bc, bg` — destructuring six breaks `subst hw`); then `resumed.globals = bodyPost.globals`,
   `evaluateHOLFiniteState resumed wdDecP = (…, inner)`, `wdDecP_globals_frame` for
   `inner.globals`, finally `post.globals = inner.globals`.
   `alloc_decCall_returned` (HtabGrowFrame) packages most `resumed` facts but lacks
   `post.globals`.

## Remaining statement-46 work

* `Cmp.less` is **signed**: derive unsigned-smallness of `nwd`/`i` (`toNat < 2^63`) from the
  real input count / allocation invariant before using an unsigned loop rank.
* Per-iteration `decCall_window` (`hbody` = `rlpEncodeWithdrawal_window`, `hcont` = the two
  slice stores via `evaluate_wordStore_memory_frame`).  Do **not** use
  `BoundWordStoreChainFrame` directly: it binds locals only, while the slice addresses come
  from the global `wd_rlp_slices`; use `evaluate_store_control_frame` plus a one-line
  `store_globals` lemma (store result is `{state with memory := …}`, so globals are
  definitionally preserved) or add a globals-pinned chain.
* Then the `while` invariant, and `source_wd_slice_loop` from
  `HeaderWithdrawalLoopFrame.lean` closes statement 46.
