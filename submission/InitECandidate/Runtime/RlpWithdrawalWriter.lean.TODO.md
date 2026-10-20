# encode_withdrawal_rlp window: what is done and what remains

Done (all checked green by `pcheck.sh Runtime.RlpWithdrawalWriter`, axioms
`propext, Classical.choice, Quot.sound`, no `sorry`):

* `wdFinishTail_window` — `p := p + w`, `rlp_finish_list`, `return {buf,total}`.
* `wdCall36_window` — amount word (`withdrawalWord36`) call + tail.
* `wdCallBytes_window` — 20-byte address field call + tail.
* `wdCall8_window` — second record word call + tail.
* `wdAssign8_window` — offset advance and the remaining chain.
* `wdCall0_window` — first record word through the destructuring `decCall`.
* `wdDecP_window` — `p := buf + 9` and the whole writer chain.

Each has the shape

    (eval t SUFFIX).2.memory w = t.memory w

under `¬ MWin B 64 w`, `B.toNat + 64 < 2^64`, `p = B + ofNat K` with the
tight offset budget (`K ≤ 48` for the amount word, `K ≤ 27` for the address
field, `K ≤ 18` for the second word, `K ≤ 9` for the first), locals
`buf ↦ B`, `p ↦ P`, `wd ↦ W`, and `code = originalRuntimeCode`.

The record-word arguments are deliberately left abstract: if the load fails the
call returns `.error` and memory is untouched; if it succeeds the shape check
inside `lookupCodeHOLExact` makes the value a word (`rlpEncodeWord_second_word`
does the extraction), so no record-read hypothesis is needed anywhere.

Remaining:

1. the `alloc` level: `.decCall "buf" .one "alloc" [.const 64] (dec p …)`.
   It needs "the alloc body preserves memory in every outcome"
   (`alloc_body_returned` gives it only for the `.returned` case; the failure
   path reduces to a `trap_with` call — `evaluate_allocationAfterPointer_failure`
   already identifies that reduction, a memory frame for the trap call is the
   missing piece).
2. the top-level `rlpEncodeWithdrawal_window :
   (eval t (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp)).2.memory w
     = t.memory w` composing 1 with `wdDecP_window`.
