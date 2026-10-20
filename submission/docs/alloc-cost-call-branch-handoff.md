# .call branch handoff (WIP at /tmp/wip-callbranch.lean.txt, HEAD green 0c46b2c86)

KEY LESSON: do NOT `rw [wordPathWork]` at the top of the `.call` branch. Lean leaves
`match some locs with ...` syntactically unreduced in the goal, and then every later
`rw`/`simp only [...]` inside that match binder fails ("Did not find an occurrence of
the pattern" / "made no progress"). Use the pre-proved per-arm lemmas instead; they take
the state `t` and the guard facts, so the goal stays folded and no match reduction is needed.

All lemmas take `(t : State)` and guard facts:
- getVars_none, badDest, findCode_none                      : = 1
- none_handler, none_clock_zero, returning_dom, returning_cut_none,
  returning_clock_zero                                      : = 1
- result_mismatch, result_pop_none, result_dom_false,
  other_result, exception_none_handler, exception_loc_mismatch : = 1 + W prog entry
- unfold_noreturn, unfold_result, unfold_exception          : fully unfolded
- *_sValEq_variant (noreturn/result/exception)              : the whole folded equality,
  taking ihBody (+ transport facts) - PREFER THESE for the three leaves.
- result_at / exception_at : whole folded equality with hfix/hfixT/hpop/hpopT/hdom/hdomT
  + ihBodyAt/ihRetAt/ihHandAt.

Remaining fixes for /tmp/wip-callbranch.lean.txt:
1. Result arm: hoist the stack analysis BEFORE splitting on hnl:
   cases hmstk : middle.stack (nil => contradict hkeyT) ; cases hstt : st (nil => contradict hkeyT) ;
   cons/cons => popEnv_agree gives popped, hpop, hpopT={popped with stack:=u}; then
   - hnl                => rw [result_mismatch (t:=s) ..., result_mismatch (t:={s with stack:=xs}) ..., ihBodyAt]
   - ¬hnl, hdom         => exact result_at ... (as written)
   - ¬hnl, ¬hdom        => rw [result_dom_false (t:=s) ... hpop hdomF,
                                result_dom_false (t:={s with stack:=xs}) ... hpopT (hdomF for popped.locals), ihBodyAt]
   (delete the popEnv=none arm entirely - impossible since st is a cons.)
2. Exception arm, handler = some, ¬hdom: missing lemma - ADD
   `wordPathWork_call_exception_dom_false` (copy exception_loc_mismatch statement/proof,
   replace hloc by `hdom : ¬ sptDomainEqUnion middle.locals envs.1 envs.2`, conclude = 1 + W),
   then rw both sides + ihBodyAt.
3. noreturn leaf / exception-none / other_result arms: use the *_sValEq_variant lemmas or
   the = 1 + W lemmas + htrans (htrans = ihBodyAt in the entry-callEnv form, obtained from
   callEntry_stack_swap hfr1 + sValEq_cons_self + the recursive dispatch).
