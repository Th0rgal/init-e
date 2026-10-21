# The actual SSA compile-output execution-cost theorem

Root's review of `b30feb1db` was correct: the `wec_stage_call_case` /
`wec_stage_loop_case` wrappers took the very cost equalities (and the callee /
body-transfer components) that the compiler proof has to *derive*.  They are
dropped.  What follows is the theorem the transfer must actually be, stated
against the real compiler API, with every target-side fact obtained from
`ssaSimulation` rather than supplied.

## Real API (inspected, not assumed)

- `Flapjack.WordAlloc.ssaCcTrans` (`WordAlloc/SSACcTrans.lean:24`)
  `: WordLangProgHOL (BitVec width) → Spt Nat → Nat →
     List (Spt Nat × Spt Unit × Spt Unit) →
     WordLangProgHOL (BitVec width) × Spt Nat × Nat`
  — the literal `ssa_cc_trans`, recursing structurally on its program and
  returning the compiled program together with the extended SSA map and the
  next fresh variable.
- `ssaSimulation p source target ssa next tables` — the compiler's own semantic
  simulation predicate, produced for each constructor by
  `ssaCcTransCorrectInstBinop`, `ssaCcTransCorrectInstLongMul`,
  `ssaCcTransCorrectInstSubOverflow`, `ssaCcTransCorrectCodeBufferWrite`,
  `ssaCcTransCorrectDataBufferWrite`, `ssaCcTransExpCorrect`, and the control
  codec lemmas (`ssaCcTrans_break_decoderClosure`,
  `ssaCcTrans_continue_decoderClosure`, …).
  Its hypothesis shape (e.g. for `inst`/`arith`/`binop`):
  `wordStateEqRel source target ∧ ssaLocalsRel next ssa source.locals target.locals
   ∧ isAllocVar next ∧ everyVarHOL … ∧ ssaMapOK next ssa ∧ ltOK tables`.
  So `wordStateEqRel` + `ssaLocalsRel` are exactly the `SsaAllocRel` I already
  use, and the code/stackSize agreement that made the callee the same syntax
  tree is part of `wordStateEqRel` itself.

## The theorem (width 64, native price)

Everything below is stated at the counter's own width, 64, and with the checked
`nativeWordPrice` instance (call `189 + 39*(args.length+1-22)` plus the
conditional `21*rets`, tail 41, moves `14/28 * length`).  There is no generic
`width` parameter: the price, the state type and the compile output all live at
`BitVec 64`.

```lean
/-- Executed-cost transfer for the actual SSA compile output. -/
theorem ssaCcTrans_executionCost_le {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (p : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact 64 C F)
    (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (hpre : wordStateEqRel source target ∧ ssaLocalsRel next ssa source.locals target.locals ∧
      isAllocVar next ∧ everyVarHOL (everyVarProgHOL p) = true ∧ ssaMapOK next ssa ∧ ltOK tables)
    (hsim : ssaSimulation p source target ssa next tables)
    (hne : (evaluate p source).1 ≠ some WordSemResult.error) :
    wordExecutionCost nativeWordPrice (ssaCcTrans p ssa next tables).1 target ≤
      wordExecutionCost nativeWordPrice p source +
        ssaTransExtra p source target ssa next tables
```

`ssaTransExtra` is defined by the **same structural recursion as `ssaCcTrans`
itself**, so it is a function of the compiled output and the reached states, not
a budget parameter:

- leaves (`skip`, `inst`, `move`, `get`/`set`/`store`, `alloc`,
  `storeConsts`, `raise`/`return`/`break`/`continue`, `tick`, `opCurrHeap`,
  `locValue`, `install`, the buffer writes, `ffi`, `shareInst`): the node-price
  difference `price (compiled) target - price p source`, truncated at zero — the
  checked `wec_skip`/`wec_inst`/`wec_move` equalities are exactly the lemmas
  that turn the left side into that difference;
- `.seq f g`: `price` node difference plus
  `ssaTransExtra price f source (reached middle) … + ssaTransExtra price g
  (reached middle) target (reached middle) …`, the middles being the actual
  `fixClock` results (checked: `wec_seq_stage_none`);
- `.ite`: the node difference plus the extra of the taken branch at the same
  state (the pair-valued read `(getVar reg s, getVarImm operand s)` must be
  rewritten as a whole — this is the open Lean obstruction);
- `.loop`: the node difference plus the recursive extra per executed iteration
  at the source clock — this is exactly `wecLoopExtra`, already checked;
- `.call`: the compiled call's node price difference plus the extra of the
  **compiled callee**, i.e. `(ssaCcTrans callee ssa' next' tables').1` for the
  source callee `callee`, at the reached entry/popped states that
  `ssaSimulation` itself produces.  Two corrections to my earlier wording:
  `tables : List (Spt Nat × Spt Unit × Spt Unit)` is **not** a code map - it is
  the list of per-constructor SSA maps with cut-set bookkeeping, threaded by the
  compiler; the callee itself is a strict subterm of `p`, so the compiled
  callee is a strict subterm of the compiled program and the call case is a
  genuine descent of the source measure (call pushes an environment and does not
  decrease the source clock, so the descent is the `termdep`/`sizeOf` component
  of `lex3_induction`, not the clock).  The `wordStateEqRel` projections on
  `code`/`stackSize` are what let the *lookup* of that callee agree on both
  sides (`stage_findCode`); they do not supply the callee's cost.

## Why this is the right shape

The conclusion mentions only `ssaCcTrans p … .1`, the source execution and
`ssaTransExtra`; no target-run cost, no target budget, no `hcall`, no `hkey`,
no whole-program maximum appear.  `hpre` is the compiler's *actual input prerequisite* (the hypothesis bundle the
`ssaCcTransCorrect*` lemmas take), not just `ssaSimulation`: the relation, the
SSA map well-formedness, the freshness bound and the table invariant. The only
premise about the target's *run* is `ssaSimulation`, which the compiler proof already establishes constructor by
constructor, and the induction is the source-measure one
(`lex3_induction`, quantified over all target programs/states/relations).
