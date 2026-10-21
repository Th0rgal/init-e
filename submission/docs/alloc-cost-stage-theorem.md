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

## Compiler-derived inserted-move counts (allocation side)

Read from the allocator sources, not assumed:

- `fixInconsistencies prio ssaL ssaR na`
  (`WordAlloc/SSAFixInconsistencies.lean:65`) returns
  `(.seq (.move (priority prio true) lmov) lseq,
    .seq (.move (priority prio false) rmov) rseq, na'', ssaL'')`
  where `varUnion := (sptToAList (sptUnion ssaL ssaR)).map Prod.fst`,
  `(lmov, rmov, na', ssaL', ssaR') := mergeMoves varUnion ssaL ssaR na`, and
  `(lseq, rseq, …) := fakeMoves prio varUnion ssaL' ssaR' na'`.  So a merge
  inserts **exactly two `.move` nodes** (one per side) plus the fake-move
  sequences, and their pair counts are the counts produced by `mergeMoves` /
  `fakeMoves` over the live-variable key list `varUnion`.
- `mergeMoves` per key: both sides located ⇒ a `seq` with a single-pair `.move`
  per divergent side; one side only ⇒ `lmove = .seq seqL (.move … [(na', lx)])`
  plus `rmove = .seq seqR (fakeMove na')`; neither ⇒ the sides pass through
  unchanged.  `fakeMove na'` is a single-pair move on the fresh name.
- Pricing: every inserted move is a `.move` node, so it costs the checked
  `nativeWordPrice_move`, `(if len ≤ 1 then 14 else 28) * len`.  Hence with
  `n := varUnion.length` live variables at the merge, the inserted move cost is
  at most `28*lmov.length + 28*rmov.length + Σ_{fake} 14 ≤ 56*n + 14*n = 70*n`,
  and exactly computable from the `mergeMoves`/`fakeMoves` outputs.

### Three different move charges, not to be conflated

1. **SSA inserted moves** — the `mergeMoves`/`fakeMoves`/`fixInconsistencies`
   programs above, priced per `.move` node by pair count (14 or 28 per pair).
2. **Stack-level `stackMove`** — `Flapjack/Stack.lean:242`
   `stackMove : Nat → Nat → Nat → Nat → StackProg α → StackProg α` emits one
   move per word via the recursive `.seq (.move …) (stackMove count (start+1)
   …)`, so `count` words cost `count` stack moves; `stackAlloc count` builds
   this at frame offset.  This is the frame/stack side, not the SSA side.
3. **`stackArgs39` spill** — 39 per spilled call argument at the allocated call
   site, which is why the call's pre-allocator term is
   `189 + 39*(args.length+1-22) + (21*rets if returning)` and the *spill* is a
   separate allocator-side extra covered by `ssaTransExtra`, never added to the
   source-side `argCost`.

Ret- and live-move counts are thus: live moves = the `mergeMoves`/`fakeMoves`
pair counts at each merge (bounded by `70*n` per merge as above); return moves
at a returning call = the moves in the allocated continuation between the
returned-value store and the continuation's first read, which the call stage's
continuation leg covers at the compiler's own reached popped state.

## Quantitative simulation and the seq induction case (current state)

`quantSsaSimulation prog source target ssa next tables extra` is the compiler's
`ssaSimulation` (`SSASemanticControl.lean:12`) plus one conjunct: the executed cost of the
ACTUAL compiled program `(ssaCcTrans prog ssa next tables).1` on the target state is at most
the source program's cost on the source state plus `extra`. It keeps the source permutation
witness, the actual runs, the outcome equality, `wordStateEqRel` and the `none`-branch
`ssaLocalsRel` unchanged, and prices everything by `refinedWordLocalPrice` (the canonical
target price: `12 * (parmove (physPairs pairs)).length` for a move, `23`/`2`/`41` for
ite/loop/non-returning call, `0` for a seq).

### What is proved

- `ssaCcTrans_seq_transfer_compiled`: the compiled-syntax `seq` transfer, derived through
  `ssaCcTrans_seq_shape` (threaded first/second outputs), the reached-pair split, and
  `refinedWordLocalPrice_seq_zero`;
- `seq_transfer_refined` / `seq_transfer_escape_refined`: the two outcomes at the canonical
  price, the escape side charging no suffix;
- `canonical_move_price_le_table`: `refinedWordLocalPrice (.move pri pairs) s <=
  allocMovePrice pairs` whenever finite-auth's `goSeq` accepts the node, i.e. the coalescing
  table bounds exactly the canonical price of the emitted move node;
- `move_seq_no_differential`: a move node present on both runs contributes zero differential.

### The obstruction in the seq induction case

`quantSsaSimulation` binds the run with `let sourceRun := evaluate prog {source with permute
:= permutation}`, so after `dsimp` the scrutinee inside its `match` is the fully expanded
record literal, while the goal obtained by `if_neg` has the scrutinee in `evaluate ... {source
with permute := ...}` form. The two are definitionally but not syntactically equal, so the
`ssaLocalsRel` component cannot be transported with `exact` (the outcome equality and
`wordStateEqRel` components do go through). `set`/`generalize` do not catch the occurrence
because it is syntactically different.

### The fix

State the predicate with the two runs as explicit existential variables and the equations as
conjuncts, e.g.

    exists permutation, exists sourceRun targetRun,
      evaluate prog {source with permute := permutation} = sourceRun
      /\ evaluate (ssaCcTrans prog ssa next tables).1 target = targetRun
      /\ (sourceRun.1 = some .error /\ True \/
          sourceRun.1 = targetRun.1 /\ wordStateEqRel sourceRun.2 targetRun.2
          /\ (match sourceRun.1 with | none => ... | _ => True)
          /\ cost bound)

Then the `match` scrutinees are variables on both sides and the transport is `rw`/`subst`.
With that in place the seq case follows as: from the first body's quantitative IH, the
outcome equality gives `targetRun = (none, midT)` whenever the source falls through (so `hT`
and `midT` are obtained, not assumed); the second body's IH is instantiated at the threaded
`secondOut` of `ssaCcTrans_seq_shape` and at the reached middles; `ssaCcTrans_seq_transfer_compiled`
composes the cost; `seq_transfer_escape_refined` covers the escaping outcome.

## Resolution: the quantitative predicate CONJOINS the cost

The refactor recorded above (explicit `sourceRun`/`targetRun` existentials) was implemented and
it exposed why hand-restating the post relation cannot work: `ssaSimulation`'s outcome match is
not just `none => ssaLocalsRel | _ => True`.  Its real shape is a match on the run's first
component with four branches --- `none => ssaLocalsRel`, `break n` and `continue n` =>
`strongLocalsRel` looked up through `tables[n]?`, and `some val => locals equality` --- carrying
`strongLocalsRel`, `sptDomain`, and table indexing.  Any hand-written copy of that relation is a
duplicate of the compiler's semantics, and the transport step fails precisely because the copies
are not syntactically identical.

So `quantSsaSimulation` is now stated as the conjunction

    ssaSimulation prog source target ssa next tables
      ∧ wordExecutionCost refinedWordLocalPrice (ssaCcTrans prog ssa next tables).1 target
          ≤ wordExecutionCost refinedWordLocalPrice prog source + extra

i.e. the compiler's component verbatim (source permutation witness, actual runs, outcome
equality, the full post match) plus exactly one new conjunct: the executed cost of the ACTUAL
compiled program at the canonical price, against the source program's cost.

- `quantSsaSimulation.toSsaSimulation` is a projection (`h.1`) --- no post-relation transport;
- `quantSsaSimulation.costBound` extracts the cost half (`h.2`), which is what the stage
  compositions consume.

Both are green with axioms `propext`/`Classical.choice`/`Quot.sound`.  This keeps the witness and
the post relation faithful by construction instead of by transcription, and it makes the seq case
purely a matter of the two compositions that already exist:
`ssaCcTransCorrectSeq` for the simulation half and `ssaCcTrans_seq_transfer_compiled` (fall-through)
/ `seq_transfer_escape_refined` (escape) for the cost half.

## Applied: runs exposed, post relation untouched

`quantSsaSimulation` now carries, existentially:

    permutation : Nat -> Nat -> Nat
    rS sS rT sT
    evaluate prog {source with permute := permutation} = (rS, sS)          -- source run
    evaluate (ssaCcTrans prog ssa next tables).1 target = (rT, sT)        -- compiled run
    ssaSimulation prog source target ssa next tables                      -- post relation, verbatim
    rS = rT                                                               -- outcome equality
    wordExecutionCost refinedWordLocalPrice (ssaCcTrans prog ssa next tables).1 target
      <= wordExecutionCost refinedWordLocalPrice prog source + extra       -- executed cost

The post relation is NOT transcribed: the compiler's own `ssaSimulation` is a conjunct, so the
four-branch outcome match (`ssaLocalsRel` / `strongLocalsRel` via `tables` / locals equality) stays
exactly as the compiler states it.  The runs are now equations over existential variables, which is
what a stage needs: `targetRun` yields `evaluate (ssaCcTrans ...).1 target = (rT, sT)`, so a stage
reads off the reached state instead of guessing it.

Accessors, all green:
- `quantSsaSimulation.toSsaSimulation` --- the compiler's simulation (projection of the conjunct);
- `quantSsaSimulation.costBound` --- the executed-cost half;
- `quantSsaSimulation.targetRun` --- the compiled run equation (reached state).

Remaining for the seq case: from the first body's quantitative IH, `rS = none` together with
`rS = rT` gives the compiled first body's outcome `none`, hence the reached middle state via
`targetRun`; feed that as `hT`/`midT` to `ssaCcTrans_seq_transfer_compiled` (fall-through) or use
`seq_transfer_escape_refined` when the outcome is not `none`; the simulation half is
`ssaCcTransCorrectSeq` applied to the two recursive IHs and the invariants.
