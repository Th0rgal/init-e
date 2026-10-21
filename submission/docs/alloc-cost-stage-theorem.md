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

## Blocker 1 cleared: `fixClock` preserves the result

`fixClock old step = (step.1, {step.2 with clock := ..., termdep := old.termdep})`, so

- `fixClock_fst : (fixClock s p).1 = p.1`
- `fixClock_fst_none : p.1 = none -> (fixClock s p).1 = none`

both proved (axioms `propext` only).  Hence a run equation `evaluate f s = (r, s')` with `r = none`
yields the `fixClock` premise the counter-based transfer needs, with middle state
`fixClockMid s (evaluate f s) := (fixClock s (evaluate f s)).2`.

## Remaining friction for the seq induction: the permutation state

`ssaSimulation` (and therefore `quantSsaSimulation`) evaluates the SOURCE program at
`{source with permute := permutation}` --- the estimator writes its register renaming into the
`permute` field --- while the counter transfer `ssaCcTrans_seq_transfer_compiled` is stated at the
plain `source`.  Instantiating the transfer at `{source with permute := permutation}` removes the
mismatch for the RUNS (via `fixClock_fst` plus the IH's `rS = none` and `rS = rT`), but the two
sides of the cost inequality then sit at different states:

    wordExecutionCost refined compiled target <= wordExecutionCost refined first {source with permute := perm} + ...

whereas the theorem wants `... <= wordExecutionCost refined (.seq first second) source + ...`.
`refinedWordLocalPrice` is state-independent, but `wordExecutionCost` is not: its `.ite` clause reads
`getVar`/`getVarImm` from the state, so a permutation that moves a compared register changes the
charged cost.  The honest options are (a) a cost-invariance lemma for `wordExecutionCost` under
`permute`-only state changes (true if `permute` is not consulted by `getVar`), or (b) charging the
source side at the permuted state and carrying the permuted state through the statement.  Option (a)
is the one to prove; it needs the fact that `getVar`/`getVarImm` ignore the `permute` field.

## Where the constructors stand (after the seq case)

DONE.  `ssaCcTrans_seq_quant_none` and `ssaCcTrans_seq_quant_escape` are the seq induction case for
both outcomes.  From the two recursive quantitative IHs they derive, at `refinedWordLocalPrice`:

- the reached middles: `midS`/`midT` are the `fixClock`ed states of each side's first-body run
  (`fixClock_fst`, `fixClock_fst_none`, `fixClockMid`), obtained, not assumed;
- the composite runs: `evaluate_seq_none` / `evaluate_seq_escape`, with `ssaCcTrans_seq_shape`
  rewriting the compiled program to `.seq firstOut secondOut` first;
- the post relation: `ssaCcTransCorrectSeq` from `firstIH`/`secondIH`/`hinv`;
- the counter bound: the counter's seq split on both sides, both node prices cancelled by
  `refinedWordLocalPrice_seq_zero`, then the two IH cost bounds.
The second body's IH is instantiated at `midS`/`midT` AND at the threaded allocator state
`(ssaCcTrans first ssa next tables).2.1/.2.2`.

ITE.  Local content complete: `evaluate_ite_true`/`_false` (the evaluator's `.ite` clause has no
`fixClock`), `refinedWordLocalPrice_ite = 23`, `wec_ite_true_canonical` (cost = 23 + selected branch),
`ite_transfer_then/else_canonical` (node price cancels), and `ite_stage_then/else` which package, for a
source ite and a compiled ite with possibly renamed condition registers, both runs plus the counter
bound.  What is missing for the quantitative case is one allocator-side fact: the compiled branch is
`body` FOLLOWED BY the inconsistency-fixing suffix
(`ssaCcTrans_ite_shape`: `.seq (ssaCcTrans first ssa na lt).1 (fixInconsistencies (mkPrio ...) ... ...).1`),
so the branch's quantitative predicate needs a canonical-price bound for that suffix (or the existing
`siteBound`/`callAfterMoves` accounting).  Requested from finite-auth in both acceptable forms.

LOOP / CALL.  The prices are proved (`refinedWordLocalPrice_loop = 2`,
`refinedWordLocalPrice_call_none = 41`), but their counter clauses are not price-only:
`.loop` is `cutState (names, .ln) s`, then `wordExecutionCost body cutSource`, then a `fixClock
cutSource (evaluate body cutSource)` split and a `wordSemContLoop` continuation test
(WordExecutionCost.lean:33), and `.call` is `getVars args s`, then `wordSemBadDestArgs`, then
`wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize`, each of the failing paths
charging only `price p s` (WordExecutionCost.lean:44).  So their quantitative cases need the same
`prime`-level splits the seq case used, with `cutState`/`fixClock` for the loop and the frame
lookup for the call; the `41` is the node price, not the total.

## The suffix certificate: what is proved and the one remaining instantiation

PROVED (all green, axioms propext/Classical.choice/Quot.sound):

- `move_fallthrough` : `(moves.map Prod.fst).Nodup` and `getVars (moves.map Prod.snd) s <> none`
  imply `(fixClock s (evaluate (.move pri moves) s)).1 = none`.  Note WHICH hypotheses: Nodup is a
  program property, and the getVars side is a state property supplied by `ssaLocalsRel` / `ssaMapOK` /
  `everyVarHOL`.  The move table is NOT used here: `goSeq_move` bounds the price
  (`12 * |parmove| <= allocMovePrice`), it says nothing about the run.  So the fall-through half of the
  certificate comes from the SSA invariants, and only the price half comes from the table.
- `seq_fallthrough` : fall-through composes over seq.
- `wec_move_state_independent`, `wec_skip_state_independent`, `wec_seq_state_independent` (the last one
  takes the fall-through hypothesis of its first half - without it the statement is FALSE, because a
  move whose sources are missing returns `some .error` and then the second half of a seq is charged on
  one state and not the other).
- `suffix_seq_cost_independent` : at the shape `fixInconsistencies` actually returns,
  `.seq (.move (priority prio true) lmov) lseq` (SSAFixInconsistencies.lean:71), its cost is state
  independent.
- `AllocOnly` : the shape of every suffix (skip/move leaves, seq nodes), with
  `allocOnly_fallthrough` and `allocOnly_cost_independent` proved by induction over it.

REMAINING, and it is purely a term-shape problem, not mathematics: `AllocOnly` of the CONCRETE suffix,
i.e. `AllocOnly (fixInconsistencies prio ssaL ssaR na).1` and, under it,
`AllocOnly (fakeMoves prio xs ssaL ssaR na).1` by list induction.  The obstruction is that
`fakeMoves`'s cons case binds a five-way `let`/`match` on `sptLookup x ssaL'` / `sptLookup x ssaR'`
BEFORE forming the pair, so after `unfold fakeMoves; dsimp only; split` the goal asks for `AllocOnly`
of a term that is only propositionally - not definitionally - the recursive call's projection, and the
induction hypothesis therefore does not apply:

    Application type mismatch: The argument
      fakeMoves_allocOnly prio xs ?m.134 ?m.135 ?m.136
    has type AllocOnly (fakeMoves prio xs ?m.134 ?m.135 ?m.136).1 ...

The fix is to pattern-match the recursive result the same way the definition does (as
SSAFixInconsistencies.lean:69-70 matches `mergeMoves`' output), so the tuple components are the same
bound variables and the projections reduce definitionally; then apply the induction hypothesis directly.
Once that lemma exists, `allocOnly_fallthrough` / `allocOnly_cost_independent` give the suffix's run and
cost facts, and `ite_quantTransfer_then` turns them into the quantitative ite constructor.

## The quantitative transfer: what is closed (HEAD 1804d4904)

CLOSED, all green with axioms exactly {propext, Classical.choice, Quot.sound}:

1. `seq` constructor, both outcomes: `ssaCcTrans_seq_quant_none`, `ssaCcTrans_seq_quant_escape`.
2. `ite` constructor: `ssaCcTrans_ite_quant_then`, i.e. `quantSsaSimulation (.ite ...) source target ssa next
   tables extra` from (a) the compiler's `ssaCcTransCorrectIf` with its invariant IHs, (b) the selected
   branch's `quantTransfer` via `ite_quantTransfer_then`, and (c) the compiled shape equation, which is what
   `ssaCcTrans_ite_shape` gives.  NOTE for whoever continues: `ssaCcTransCorrectIf` lives in
   `Flapjack.Compiler.Backend.WordAlloc` and needs `import ...Proofs.SSASemanticIf`; without the import it
   looks like a missing lemma.
3. The compiled-branch chain, which is what makes suffix-carrying constructors composable:
   `quantTransfer` (program-parametric: source program + EXPLICIT compiled program + runs + outcome equality
   + cost bound) -> `ite_stage_then/else` (both runs and the bound in one package; the 23 node price cancels)
   -> `ite_quantTransfer_then` -> `seq_suffix_transfer` (append a suffix: fall-through keeps the outcome,
   state-independent cost makes the suffix's charge a constant) -> `compiled_branch_transfer` (suffix facts
   from `AllocOnly`) -> `fixInconsistencies_suffix_transfer` (the concrete suffix, no hypotheses about it).
4. The allocator-side certificate, derived rather than requested:
   `move_fallthrough`, `seq_fallthrough`, `wec_move_state_independent`, `wec_skip_state_independent`,
   `wec_seq_state_independent` (false WITHOUT the fall-through hypothesis - a move with missing sources
   returns `some .error`), `suffix_seq_cost_independent`, `AllocOnly` (skip/move/inst/seq) with
   `allocOnly_fallthrough` and `allocOnly_cost_independent`, `fakeMoves_allocOnly` (list induction; see the
   tuple-equation technique below), `fixInconsistencies_allocOnly`.
   The RUN half of the certificate comes from the SSA invariants (`Nodup` syntactic, `getVars` from
   `ssaLocalsRel`/`ssaMapOK`/`everyVarHOL`), NOT from the move table; only the PRICE half uses the table
   (`goSeq_move` via `canonical_move_price_le_table`).  The instruction fall-through is parameterised
   (`hinst`), since `fakeMove v = .inst (.const v 0)`.
5. Node prices complete: move `12 * |parmove (physPairs moves)|`, `ite 23`, `loop 2`, `call none 41`,
   returning call `(if handler.isSome then 189 else 63) + 39*(args+1-22) + 21*(values+1-22)`, `seq 0`.
   Plus `wec_call_none_getVars_none` / `wec_call_none_badDest` for the call's flat-price failure paths.

## Technique note: proving things about fakeMoves (cost several compiles to find)

Projecting the returned 5-tuple in a goal fights back: after `simp only [fakeMoves]` / `unfold` the goal is
`AllocOnly (...5-tuple...).1` and every argument position stays a metavariable ("typeclass instance is
stuck: NeZero ?m").  What works:

- state an auxiliary lemma carrying the tuple EQUATION as a hypothesis
  (`fakeMoves prio xs ssaL ssaR na = (l, r, na', sl, sr) -> AllocOnly l`) and recurse with the equation;
- unfold the definition inside the equation only (`simp only [fakeMoves] at h`), rewrite the recursive call
  by its own equation, so every component in `h` is a bound variable;
- `split at h`, then `injection h with h1 _` and `rw [<- h1]` to move the goal onto the first component;
- the split branches differ in shape (some return the recursive program itself, others a seq with a
  `fakeMove` or a `move` node), so try `exact ih` first, then the seq forms;
- `fakeMove`'s argument is the Nat component, not the Spt.
The projected form then follows: obtain the tuple, `rw`, `show AllocOnly p1`, apply the auxiliary lemma `rfl`.

## Remaining

- `loop`: the counter's clause is not a one-shot composition - `cutState (names, .ln) s`, then the body's
  work, then a `fixClock` split with `wordSemContLoop result` deciding whether the NEXT iteration is charged
  (zero when `middle.clock = 0`).  So its transfer needs a recursion over the loop's own clock, not the
  three-step assembly used for ite.
- `call`: flat-price failure paths are done; the successful path is `getVars` -> `wordSemBadDestArgs` ->
  `wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize`, which charges the callee - this is
  where the global transformed-callee code relation enters.

## The optimizer price (root 8e0fe4244) - ported at HEAD dd398d158

`wordOptimizerLocalPrice`: move = 24 per pair, instruction/get/loc/heap heads = max 24 (refined price),
everything else = refined price.  CSE and copy propagation are proved against it, so the transfer has to be
available there.

The port rides a seam that costs nothing: the RUN half of a transfer never mentions a price.
So `quantRuns` is price-free, `quantTransferAt price ...` pairs it with the counter bound, and
`quantRuns.of_quantTransfer` reads the run half straight out of the refined-price transfer already proved.
Only the cost half is redone, and the counter splits (`wec_seq_none_split_generic`,
`wec_seq_some_split_generic`, `wec_move_generic`, `wec_inst`, `wec_skip`) were already price-polymorphic.

Landed at the optimizer price:
- node prices `wordOptimizerLocalPrice_move/_seq_zero/_ite/_loop/_call_none` (24*pairs, 0, 23, 2, 41);
- `wec_move_optimizer` (a move node charges exactly 24*moves.length) and the two seq splits;
- the leaf state-independence facts (`wec_skip_optimizer_state_independent`,
  `wec_inst_optimizer_state_independent`, `wec_move_optimizer_state_independent`), which with the price-free
  run half are what the suffix certificate needs to compose a compiled branch at this price;
- `transformedCalleeRelAt` + `.spec`: the transformed-callee relation at ANY price, to instantiate here.

### Blocker, and it is a real factor two, not a tactic slip

The optimizer price charges 24 per move PAIR; the certified coalescing table charges 12 per emitted MOVE and
budgets 24 per NON-self pair.  A swap of two locals emits two moves, so the optimizer price can be twice the
table's charge for the same node (48n against 24n).  Hence `24 * parmove length <= allocMovePrice` is FALSE,
both at n = 1 (24 against 12) and at n >= 2 with a swap, and no sharper scheduler bound repairs it.
What is proved instead, from `goSeq_move` by arithmetic:
  optimizer_move_price_le_double_table : 24 * length <= 2 * allocMovePrice pairs
  optimizer_move_price_le_nonself      : 24 * length <= 56 * nonselfCount pairs
i.e. the inserted-move charge at the optimizer price is at most twice the certified table charge.  If the
downstream composition cannot absorb that factor on the inserted-move part, the table has to be restated at 24
per non-self pair rather than the price weakened.

### Build note

The optimizer-price oleans are not in the cost-allocation build dir.  Copy the missing ones in, e.g.
`cp -rn finite-score-build/.lake/build/lib/lean/InitECandidate cost-allocation-build/lib/lean/`, otherwise imports
such as `WordOptimizerPrice` / `WordOptimizerMoveCost` fail with "object file ... does not exist".
Also watch the LEAN_PATH: `N=$(cat shared_lean_path.txt)` is colon-separated and must not be overwritten with a
single directory while copying oleans (that mistake produced a bogus "unknown module prefix Flapjack").

## The call node is closed (HEAD 1d9bb6ccb)

`wec_call_none_success`: with the frame looked up (`wordSemFindCode dest xs s.code s.stackSize =
some (args1, prog, ss)`), a live clock and no handler, the call charges 41 plus the CALLEE's cost at
`callEnv args1 ss (decClock s)` - the environment the call constructs.

`wec_call_none_callee_transfer`: if each program's call site looks up its frame and the transformed callee
charges at most the original's plus a budget AT THE ENVIRONMENTS THE TWO CALLS CONSTRUCT, the whole call node
transfers within that budget.  The two inputs are exactly what already exists: `findCode_some_lookup` turns each
`wordSemFindCode` success into the `sptLookup` facts, and `transformedCalleeRel.spec` gives the callee bound at
those lookups.  Both sides are rewritten by the success lemma and the node price 41 cancels, exactly as the
ite's 23 does.

### What this took (each item cost a failed compile)

- the `getVars` match must be iota-reduced (`dsimp only`) after rewriting with `hgv`, else the `badDestArgs`
  `if` is buried under the match and nothing can rewrite it;
- the guard must be discharged WITHOUT rewriting `hbad` - that produces the undischargeable redex
  `if false = true` - the way is `rw [if_neg (by rw [hbad]; decide)]`;
- `wordSemAddRetLoc` must be reduced with `simp only`, not `rw`: it sits under a `generalizing := false` match;
- the clock branch is a `dite`, resolved with `dif_neg` of the live-clock hypothesis;
- the state's stack size is `Spt Nat`, i.e. the frame's third component is `Option Nat`; a generic `StackSize`
  binder fails to unify.

## Remaining: the loop constructor

The counter side is ready (`wec_loop_cutState_none`, `wec_loop_split`, `wec_loop_stop`, `wec_loop_cont`): the
loop's cost is decomposed one step per iteration with the recursive call explicit at
`(wordSemSTOP (.loop ...)) (decClock middle)`.  What the loop's transfer still needs is a genuine induction over
the loop's clock TOGETHER with the compiler's `wordStateEqRel`, because the body must transfer at every
iteration state and the recursion's state is not the caller's.  That is why the loop is not the ite's one-shot
assembly.

## The loop case: both halves done, and what the induction still needs

Landed (all green):

| cost | run |
| --- | --- |
| `wec_loop_stop_transfer` | `evaluate_loop_stop` |
| `wec_loop_cont_done_transfer` | (exhausted branch, no recursion to run) |
| `wec_loop_cont_live_transfer` | `evaluate_loop_cont` |

Cost shapes: node price 2 plus the body's work on both sides; the live-continuing shape charges one further
iteration and its budget is DOUBLED (one extra for the body, one for the recursion) - with a single extra the
statement is false, so the loop's budget must scale with the iteration count.
Run shapes: the stop case returns `wordSemExitLoop result` at the body's state (NOT the body's result), and the
`break 0` result is routed through `cutState` at `exitNames` instead, hence its explicit exclusion; the
live-continuing case recurses at `wordSemSTOP (.loop ...)` with the decremented clock, the same point the cost
side recurses at.

### Why the induction cannot be finished from the run half alone

`evaluate_loop_stop` produces `(wordSemExitLoop result, middle)` - the body's RESULT and the body's STATE. Two
iterations therefore agree on the outcome only if their states agree too, and the loop's recursion feeds `middle`
back in. So the loop's induction needs a state relation between the source and target iterations (the compiler's
`wordStateEqRel`), preserved by `cutState` and by the body's evaluation, exactly as `ssaCcTransCorrectLoop` uses
it. The run half alone is not enough, which is why the loop is not assembled from `evaluate_loop_stop/cont` by
arithmetic the way the ite was assembled from `evaluate_ite_true/false`.

### Two rewrite traps worth keeping

- after `rw [h]` on the body's `fixClock` result, a dependent `match _h : (result, middle)` does NOT reduce on
  the pair literal: `dsimp only` first (same in the call clause);
- close the continuation-flag goal with `rw [if_pos (by rw [hc])]` and do NOT append `rfl`: `rw` already
  discharges `true = true`, and the extra `rfl` then fails with "no goals to be solved" while Lean still reports
  the lemma's axioms as clean, so the error looks like it is on a different line.

## Next step: make the code relation the call case's only interface

`wec_call_none_callee_transfer` currently takes the two frames as hypotheses.  They can be made internal, leaving
`transformedCalleeRel` as the sole interface:

    theorem wec_call_none_callee_transfer_of_code
        (hrel   : transformedCalleeRel (C := C) (F := F) origCode transCode budget)
        (hcode  : s.code  = origCode)
        (hcode' : s'.code = transCode)
        (hgv, hgv', hbad, hclk, hclk' as in the existing lemma) :
        wordExecutionCost refined (.call none dest args none) s'
          <= wordExecutionCost refined (.call none dest args none) s + budget

Proof: `cases` on `wordSemFindCode dest xs origCode s.stackSize`.  The `none` case charges 41 on both sides, so
`omega`.  In the `some (args1, prog, ss)` case, `findCode_some_lookup` supplies the `sptLookup` facts, and
`transformedCalleeRel.spec` supplies the callee bound at `callEnv args1 ss (decClock s)` - exactly the two inputs
`wec_call_none_callee_transfer` asks for.  The transformed side's frame comes from the relation's own lookup, so
nothing about the target frame has to be assumed.

Doing this leaves the call case with: the code relation, the `getVars` facts, the bad-destination fact, and the
clocks.  Everything else is internal.

## The end-to-end call lemma is proved, and the code relation alone is NOT enough

`wec_call_none_callee_transfer_of_code` exists (commit ef996ed00) and takes the two frames as internal, but it
needs TWO hypotheses beyond `transformedCalleeRel`; neither is derivable from the relation:

1. `harity` - a transformed frame at a destination forces an ORIGINAL frame at that same destination and arity.
   Without it the flat path "original lookup fails, transformed succeeds" needs `cost pC <= budget`, which is
   false in general (the relation only ever bounds a callee conditioned on the original having one; it never says
   the original HAS one). With it that path is a contradiction: the transformed table cannot invent callees,
   because the arity test is the same on both sides.
2. `harg : xs = xs'` - the two argument lists agree. Needed only for `dest = none`: an INDIRECT call takes its
   destination from the block of its LAST ARGUMENT, i.e. off `xs`, so with `xs <> xs'` the two sides charge
   different callees and nothing relates them. For the direct case `dest := some d` this hypothesis is removable.

Design consequence worth keeping: the frames' argument lists and stack sizes are fully internal (the `ss`
components are never identified), which is what lets the caller supply only the code relation plus these two
facts. Supporting lemmas added: `findCode_some_frame`, `findCode_destNone_frame`, `findCode_some_of_frame`,
`findCode_destNone_of_frame` (frames <-> sptLookup at the right arity, direct and indirect).

Also recorded because it wasted a compile: `transformedCalleeRel.spec` returns `(exists ...) AND (cost <= ...)`, so
`obtain <hspec, ->` takes the WRONG component; it must be `obtain <-, hspec>`.

## The direct-call corollary: `harg` is an INDIRECT-call artefact only

`harity` is a genuine interface requirement (see above), but `harg` is not: a call with a program-counter
destination resolves its frame at `d` in BOTH tables, so the two sides agree on the destination by
construction.  The delivered form is therefore available without any argument-list hypothesis:

    theorem wec_call_none_callee_transfer_of_code_some {C F : Type}
        (d : Nat) (args : List Nat)
        (s s' : WordSemStateFiniteExact 64 C F) (xs xs' : List (WordLocW 64))
        (origCode transCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (budget : Nat)
        (hgv  : getVars args s  = some xs)   (hgv' : getVars args s' = some xs')
        (hbad : wordSemBadDestArgs (some d) args = false)
        (hclk : s.clock = 0 -> False) (hclk' : s'.clock = 0 -> False)
        (hcode : s.code = origCode) (hcode' : s'.code = transCode)
        (harity : forall (d' arity : Nat) (bodyC),
           sptLookup d' transCode = some (arity, bodyC) ->
             exists body, sptLookup d' origCode = some (arity, body))
        (hrel : transformedCalleeRel (C := C) (F := F) origCode transCode budget) :
        wordExecutionCost refined (.call none (some d) args none) s'
          <= wordExecutionCost refined (.call none (some d) args none) s + budget

So the call case's interface is: the code relation, `harity`, the two `getVars` facts, the bad-destination
fact and the two live clocks.  The two argument lists may differ (the relation's `.spec` already bounds the
callee at its own `callEnv`); what the flat path needs is only that the arity test passes on both sides,
which follows because `getVars` walks `args`, so both lists have `args.length` elements (new lemma
`getVars_length`: `getVars args s = some xs -> xs.length = args.length`).

`harg` remains necessary only for `dest = none`, where the destination is the block of the LAST ARGUMENT and
is therefore read off the state-dependent argument list: there the two sides can charge different callees,
and nothing in the code relation relates them.

Axioms: `wec_call_none_callee_transfer_of_code_some` and `wec_call_none_callee_transfer_of_code` depend only
on `propext`, `Classical.choice` and `Quot.sound`; `getVars_length` and the four `findCode_*_frame` lemmas
only on `propext`.

## The loop's clock induction is done

The loop node's transfer is now proved as a genuine induction over the loop's clock, with the iteration
states related by the compiler's `wordStateEqRel`.  All green, axioms `propext` / `Classical.choice` /
`Quot.sound` throughout:

    def LoopBodyStep (names) (body bodyC) (B : Nat) : Prop :=
      forall st ct cutS cutT resultS midS resultT midT,
        wordStateEqRel st ct ->
        cutState (names, .ln) st = some cutS -> cutState (names, .ln) ct = some cutT ->
        fixClock cutS (evaluate body cutS) = (resultS, midS) ->
        fixClock cutT (evaluate bodyC cutT) = (resultT, midT) ->
        wordSemContLoop resultS = wordSemContLoop resultT
        /\ wordStateEqRel midS midT
        /\ cost bodyC cutT <= cost body cutS + B

    def LoopCutAgrees (names) : Prop :=
      forall st ct, wordStateEqRel st ct ->
        (exists cutS, cutState (names,.ln) st = some cutS) <->
        (exists cutT, cutState (names,.ln) ct = some cutT)

    theorem wec_loop_step_transfer            -- (a) the one-step composition
        (cutState s = some cutS) (cutState t = some cutT)
        (fixClock cutS (evaluate body cutS) = (resultS, midS))
        (fixClock cutT (evaluate bodyC cutT) = (resultT, midT))
        (wordSemContLoop resultS = wordSemContLoop resultT)     -- same branch
        (midS.clock = 0 <-> midT.clock = 0)                     -- same clock guard
        (cost bodyC cutT <= cost body cutS + B)
        (cost (loop bodyC) (decClock midT) <= cost (loop body) (decClock midS) + R) :
        cost (loop bodyC) t <= cost (loop body) s + (B + R)

    theorem wec_loop_transfer_clock_aux       -- (b) strong induction over the clock
        (hbody : LoopBodyStep names body bodyC B) (hcut : LoopCutAgrees names) :
        forall n s t, s.clock <= n -> wordStateEqRel s t ->
          cost (.loop names bodyC liveOut) t <=
            cost (.loop names body liveOut) s + B * (n + 1)

    theorem wec_loop_transfer_clock           -- at the entry clock
        (hbody : LoopBodyStep ...) (hcut : LoopCutAgrees ...) (hrel : wordStateEqRel s t) :
        cost (.loop names bodyC liveOut) t <= cost (.loop names body liveOut) s + B * (s.clock + 1)

    theorem wec_loop_transfer_clock_double    -- the loose, per-iteration-2B form
        ... : ... <= ... + 2 * B * (s.clock + 1)

Support: `wordStateEqRel_clock` (`t.clock = s.clock`), `wordStateEqRel_cutState` (`cutState` rewrites only
`locals`, a field the relation ignores, so related states cut to related cut states) and
`wordStateEqRel_decClock` (both sides decrement the same clock).  The run half of the same three shapes is
`evaluate_loop_stop_pair` / `evaluate_loop_cont_pair`, i.e. `evaluate_loop_stop` / `evaluate_loop_cont`
applied on both sides - exactly the cases the cost step splits on.

Notes for whoever continues:

- **the budget must scale with the iteration count, and one iteration costs B (not 2B)**.  `wec_loop_cont_live_transfer`
  charges the SAME `extra` for the body and for the recursion, which is why its conclusion is `extra + extra`;
  that doubling is a one-step artefact: at the next level the recursion's budget is the ACCUMULATED one, not `B`.
  With the body's budget `B` and the recursion's budget `R` separated (`wec_loop_step_transfer`), one executed
  iteration adds exactly `B`, and the tight bound is `B * (s.clock + 1)`.  A constant budget - `B` or `2*B` - is
  false for the same reason: the loop recharges the body at every level.
- **the `+ 1` is real**: the cut and the body are charged before the clock is consulted, so a loop entered at
  clock 0 still executes its body once.  A bound `B * s.clock` without the `+ 1` is false.
  NOTE (superseded): `B * (s.clock + 1)` is still a FUEL shape - it charges the entry clock, not the
  iterations the run performs, and the entry clock can be arbitrarily large relative to them.  It is kept
  only as an intermediate lemma; the delivered transfer is `B * loopIterCount`, the trace's own count (see
  the iteration-count section at the end of this file).
- **both extra hypotheses are genuine**, and neither follows from `wordStateEqRel`:
  `LoopCutAgrees` because cutability reads `locals` (which the relation deliberately does not constrain), and
  `LoopBodyStep` because the body's own cost transfer at each iteration is exactly what the body's simulation
  provides.  `LoopBodyStep` is the quantitative analogue of the universal body hypothesis of
  `ssaCcTransCorrectLoop` (whose premise is `wordStateEqRel` plus the SSA invariants), so the loop's
  `quantSsaSimulation` case is: discharge `LoopBodyStep`/`LoopCutAgrees` from the compiler's body IH and
  instantiate `wec_loop_transfer_clock`.
- induction shape: `Nat.strong_induction_on` on the clock bound, with the statement at `s.clock <= n`.  In the
  live case the recursive instance is at `(decClock midS).clock = midS.clock - 1 < n`, using
  `fixClock_IMP_LESS_EQ` (`midS.clock <= cutS.clock = s.clock`) and the fact that a live middle has a positive
  clock; the arithmetic `B + B * (k + 1) = B * (k + 2) <= B * (n + 1)` is `Nat.mul_succ` plus `omega` (plain
  `omega` on the product alone fails, it needs the product as an atom plus an explicit `Nat.mul_le_mul_left`).

## The loop constructor: both hypotheses of the clock induction are DISCHARGED

`wec_loop_transfer_clock` took `LoopBodyStep` and `LoopCutAgrees` explicitly.  The constructor in
`AllocCostSSACompiledLeafBounds.lean` now DERIVES both, from a body hypothesis and one domain fact, and
composes the run half and the cost half into a `quantTransfer` (and a `quantSsaSimulation`) case.  All
green; axioms `propext` / `Classical.choice` / `Quot.sound` throughout (`sptSubsetLive_congr`: none).

### The two inputs

    noncomputable def LoopBodyTransfer (body bodyC : prog) (B : Nat) : Prop :=
      forall st ct, wordStateEqRel st ct ->
        (exists rS sS rT sT,
          evaluate body st  = (rS, sS) /\
          evaluate bodyC ct = (rT, sT) /\
          rS = rT /\                              -- same OUTCOME
          wordStateEqRel sS sT) /\                -- related REACHED states
        cost bodyC ct <= cost body st + B

    def LoopLocalsDomAgrees : Prop :=
      forall st ct, wordStateEqRel st ct -> forall key, sptMem key st.locals <-> sptMem key ct.locals

`LoopBodyTransfer` is the quantitative analogue of the universal body premise of
`ssaCcTransCorrectLoop` (`ssaSimulation body st ct map na lt` at every related pair): same universality
over `wordStateEqRel`-related pairs, plus the cost quantifier and, crucially, the run components.
`LoopLocalsDomAgrees` is the sharper form of the information `wordStateEqRel` deliberately omits (`it
lists 21 fields; locals and permutation are absent`): it is the *whole* missing fact about `locals`,
not just one cutset's worth.

### What is derived (nothing is assumed twice)

| derived | from |
| --- | --- |
| `LoopBodyStep names body bodyC B` | `LoopBodyTransfer` + `wordStateEqRel_cutState` + `fix_clock_evaluate` |
| `LoopCutAgrees names` | `LoopLocalsDomAgrees` + `cutState_exists_iff` (any cutset, not just `names`) |
| loop run agreement | `LoopBodyTransfer` + `LoopLocalsDomAgrees` (clock induction) |
| loop cost bound `B * loopIterCount ... source` | `wec_loop_transfer_iters` at the two derived hypotheses |

Support: `sptSubsetLive_congr` (subset-liveness is a domain property), `cutState_exists_iff`
(`cutState cs s` succeeds iff both name sets are live in `s.locals`), `cutState_exists_congr` (hence
cutability agrees whenever the domains do), `loopBodyStep_of_transfer`, `loopCutAgrees_of_localsDom`,
and the run shapes `evaluate_loop_cut_none` / `evaluate_loop_cont_done` / `evaluate_loop_break` (the
`break 0` case the `evaluate_loop_stop` shape excludes, because the evaluator routes it through the
EXIT cutset).

### The delivered statements

    theorem loop_quantTransfer
        (hbody : LoopBodyTransfer body bodyC B) (hloc : LoopLocalsDomAgrees)
        (hrel  : wordStateEqRel source target) :
        quantTransfer (.loop names body liveOut) (.loop names bodyC liveOut) source target
          (B * loopIterCount names body source)

    theorem ssaCcTrans_loop_quant
        (bodyIH : forall st ct map na lt, wordStateEqRel st ct /\ ssaLocalsRel na map st.locals ct.locals /\
           isAllocVar na /\ everyVarHOL (fun key => decide (key < na)) body = true /\
           ssaMapOK na map /\ ltOK lt -> ssaSimulation body st ct map na lt)
        (hinv  : <the loop's own six-conjunct premise, as in ssaCcTransCorrectLoop>)
        (hshape : (ssaCcTrans (.loop names body exitNames) ssa next tables).1 =
                    .loop names bodyC exitNames)
        (hbody : LoopBodyTransfer body bodyC B) (hloc : LoopLocalsDomAgrees) :
        quantSsaSimulation (.loop names body exitNames) source target ssa next tables
          (B * loopIterCount names body source)

`ssaCcTrans_loop_quant` mirrors `ssaCcTransCorrectLoop`'s bundle verbatim (`bodyIH` + the six premises)
for the semantic conjunct, and transports the quantitative conjuncts of `loop_quantTransfer` through
`hshape`, exactly the way `ssaCcTrans_ite_quant_then` consumes its `hshape`.  It needs the new import
`Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticLoop`.

### What does NOT discharge: the locals-domain agreement, and the real loop output shape

1. **`LoopLocalsDomAgrees` is not derivable from the invariant bundle, and must not be weakened away.**
   `wordStateEqRel` does not constrain `locals` at all, and `ssaLocalsRel` reads only the source side's
   entries, so a related pair can have locals with different domains.  This is machine-checked, not
   asserted: `loopLocalsDomAgrees_refuted` proves

       not (forall st ct, wordStateEqRel st ct -> ssaLocalsRel 0 Spt.ln st.locals ct.locals ->
              forall key, sptMem key st.locals <-> sptMem key ct.locals)

   by exhibiting the pair `st.locals = Spt.ln`, `ct.locals = sptInsert 0 (.word 0) Spt.ln` (the SSA
   relation holds vacuously because the source side has no entries).  Composing with the PROVED
   `cutState_exists_iff` gives the precise missing conjunct: cutability, i.e. `sptSubsetLive`, i.e.
   `forall key in names, sptMem key locals`, and `sptMem 0` differs across that pair.  That is why the
   failing goal, at the point where the induction needs it, is exactly

       forall key : Nat, sptMem key st.locals <-> sptMem key ct.locals

   with only `hrel : wordStateEqRel st ct` in context - no field of the relation mentions `locals`.
   The hypothesis is therefore kept explicit and *sharper* than before: one domain fact per related
   pair replaces the per-cutset `LoopCutAgrees`.
2. The literal `ssaCcTrans` output for a loop is NOT a `.loop` node: it is
   `.seq setup (.loop (renamed names) (body ++ reconcile moves) (renamed exits))`
   (`ssaCcTrans_loop_output` in `AllocCostSSABodyWork.lean`), and the setup program runs BEFORE the
   loop.  Hence `hshape` is an interface hypothesis, as the ite constructor's is; composing with the
   setup's cost and with the renamed cutset's cutability on the post-setup state is the remaining
   (separate) setup/renaming step, not a gap in this constructor.

### Proof notes for whoever continues

- `fix_clock_evaluate : fixClock s (evaluate p s) = evaluate p s` - a run's own result is already clock
  fixed, so on a run hypothesis `evaluate p s = (r, s1)` the `fixClock`-shaped hypothesis of
  `LoopBodyStep` is just `rw [fix_clock_evaluate s p]; exact hrunS`.  Do NOT try to rewrite
  `fixClock s (r, s1)` with it : after the `rw [hrunS]` the pattern is gone.
- the evaluator's loop clause is a DEPENDENT match on `cutState`, so `rw [evaluate]` then `split` yields
  the two cut branches; in the failing branch the goal is closed by `rw [hs] at hnone; cases hnone`,
  and in the succeeding branch the goal still contains `match _h : cutSource.fixClock (evaluate body
  cutSource)` - rewrite with the run hypothesis, `dsimp only`, then the `dite` on the clock.
- `break 0`: `cases hbrk` (`hbrk : result = some (.break 0)`) substitutes the result everywhere, which
  is what reduces both the `wordSemContLoop` test and the following result match; then
  `rw [if_neg (by decide)]` and `rw [hcut]` followed by `rfl` (the match on `some s2` needs the final
  `rfl`, not a `dsimp`, which reports "no progress").
- `t; u` vs `t` newline `u`: `;` applies `u` to EVERY goal `t` produced - writing
  `rw [hs] at hnone; cases hnone` in a branch is fine, but the same tactic closed a second branch's
  goals in an earlier draft, producing a spurious "unsolved goals".  Use newlines inside `next`
  branches of a `split`.

## The loop's budget is counted in EXECUTED iterations, not in the entry clock

`B * (s.clock + 1)` is a FUEL bound: it charges the entry clock, and at the composition stage the entry
clock can be arbitrarily larger than the iterations a run actually performs.  The loop's quantitative
transfer is therefore stated, and proved, against the trace's OWN iteration count.  Everything is at
`wordExecutionCost refinedWordLocalPrice`; the clock-shaped `wec_loop_transfer_clock` /
`wec_loop_transfer_clock_double` remain in the file as intermediate lemmas only.

### The count is the trace

    noncomputable def loopIterCountAux (names) (body) : Nat -> state -> Nat
      | 0, s   => match cutState (names, .ln) s with | none => 0 | some _ => 1
      | n + 1, s =>
          match cutState (names, .ln) s with
          | none => 0
          | some cutS =>
            match fixClock cutS (evaluate body cutS) with
            | (res, mid) =>
                if wordSemContLoop res then
                  (if mid.clock = 0 then 1 else 1 + loopIterCountAux names body n (decClock mid))
                else 1

    noncomputable def loopIterCount (names) (body) (s) : Nat := loopIterCountAux names body s.clock s

This is literally the recursion the evaluator's `.loop` clause takes, so every step of it is one
iteration the run performs: the cut is consulted first (a failed cut runs NOTHING - no charge, no body),
one body execution costs one unit, and the only recursion is at `decClock mid`, i.e. the next iteration's
state.  The `Nat` argument is FUEL FOR THE PROOF ORDER ONLY, never for the accounting: it is always at
least `s.clock` (`loopIterCount` passes exactly `s.clock`), one iteration consumes exactly one unit
because `decClock` decrements the clock, and the clause at an exhausted clock is the `mid.clock = 0`
branch, which terminates the count with `1`.  So the fuel never truncates a trace: the theorem is always
instantiated at `s.clock <= n`.

Trace facts, both proved:

    theorem loopIterCount_le_clock_succ : loopIterCount names body s <= s.clock + 1

- an executed iteration costs `B` even at an exhausted clock (`mid.clock = 0`), which is the ONE extra
  iteration relative to the entry clock: the cut and the body run BEFORE the clock is consulted, so a
  loop entered at clock 0 executes one iteration.  That is exactly what made `B * clock` false; in
  executed-iteration terms it is a property of the trace (the `+ 1` above), not a fuel allowance.

### The transfer

    theorem wec_loop_transfer_iters_aux
        (hbody : LoopBodyStep names body bodyC B) (hcut : LoopCutAgrees names) :
        forall n s t, s.clock <= n -> wordStateEqRel s t ->
          cost (.loop names bodyC liveOut) t <=
            cost (.loop names body liveOut) s + B * loopIterCountAux names body n s

    theorem wec_loop_transfer_iters
        (hbody : LoopBodyStep names body bodyC B) (hcut : LoopCutAgrees names)
        (hrel : wordStateEqRel s t) :
        cost (.loop names bodyC liveOut) t <=
          cost (.loop names body liveOut) s + B * loopIterCount names body s

Proof: induction on the FUEL (which mirrors the trace exactly, so the recursive instance is at the
`decClock` middles and their own count), with the three one-step shapes already available
(`wec_loop_stop_transfer`, `wec_loop_cont_done_transfer`, `wec_loop_cont_live_transfer`) supplying the
single-iteration transfer.  The count equation at each step is the definitional unfolding
(`loopIterCountAux_succ`, `loopIterCountAux_zero`, proved by `rfl`), reduced with
`simp only [..., hs, hRunS, hc]`, plus `if_pos`/`if_neg` on the middle's clock and
`Bool.false_eq_true` for the `wordSemContLoop ... = false` condition.

### The delivered constructors now use it

`loop_quantTransfer` and `ssaCcTrans_loop_quant` conclude with budget
`B * loopIterCount names body source`: no clock, no multiplier, no floor.  Their other inputs are
unchanged (`LoopBodyTransfer`, `LoopLocalsDomAgrees`, and for the `quantSsaSimulation` form
`bodyIH` + the six-conjunct premise + `hshape`), and the run half (`evaluate_loop_outcome_agree`) is
untouched because the outcome agreement does not depend on the budget at all.

Axioms: `loopIterCountAux_succ`, `loopIterCountAux_zero`, `loopIterCountAux_le_clock`,
`loopIterCount_le_clock_succ`, `wec_loop_transfer_iters_aux`, `wec_loop_transfer_iters`,
`loop_quantTransfer`, `ssaCcTrans_loop_quant` all depend only on `propext`, `Classical.choice` and
`Quot.sound` (the two count equations inherit `Classical.choice` from the noncomputable count; the
recursion itself is structural).

One trap worth keeping: the count's match must be REDUCED, not rewritten - `rw [loopIterCountAux_succ,
hs]` leaves the `match some cutS with ...` unreduced (the pattern variable shadows), while
`simp only [loopIterCountAux_succ, hs, hRunS, hc]` performs the iota steps.

## The loop at the compiler's literal output shape (`.seq setup (.loop ...)`)

`ssaCcTrans_loop_output` settles what the loop clause really emits: the setup program is INSERTED and
runs BEFORE the loop, so the compiled program is `.seq setup (.loop ssaNames bodyFinal ssaExit)`
while the source is the bare loop node.  The composition is therefore ASYMMETRIC - the compiled side
is a `seq`, the source side has no partner for the setup to charge against - so it is done once in the
program-parametric `quantTransfer` language and then transported through the shape, exactly the way
`ssaCcTrans_ite_quant_then` consumes its `hshape`.  All green at
`wordExecutionCost refinedWordLocalPrice`; axioms `propext` / `Classical.choice` / `Quot.sound`
(`ssaCcTrans_loop_output_shape`: `propext` / `Quot.sound`).

    theorem seq_inserted_prefix_quantTransfer
        (hT   : fixClock target (evaluate setup target) = (none, post))  -- the setup falls through
        (hs   : quantTransfer srcProg compiledProg source post extraLoop)  -- the loop at the post-setup pair
        (hc   : wordExecutionCost setup target <= extraSetup)             -- the setup's own charge
        : quantTransfer srcProg (.seq setup compiledProg) source target (extraSetup + extraLoop)

    theorem ssaCcTrans_loop_seq_quant
        (bodyIH) (hinv)                                  -- the loop's semantic half, bundle unchanged
        (hshape : (ssaCcTrans (.loop names body exitNames) ssa next tables).1 =
                    .seq setup (.loop names bodyC exitNames))
        (hsetup : fixClock target (evaluate setup target) = (none, post))
        (hsetupCost : wordExecutionCost setup target <= extraSetup)
        (hrelPost : wordStateEqRel source post)
        (hbody : LoopBodyTransfer body bodyC B) (hloc : LoopLocalsDomAgrees) :
        quantSsaSimulation (.loop names body exitNames) source target ssa next tables
          (extraSetup + B * loopIterCount names body source)

    theorem ssaCcTrans_loop_output_shape                     -- the compiler's literal output, as a shape
        (setupEq : loopSetup names exits ssa next = (setup, ssaRefreshed, nextRefreshed))
        (namesEq : ssaNames = applyNummapKey (optionLookup ssaRefreshed) names)
        (exitsEq : ssaExit = applyNummapKey (optionLookup ssaRefreshed) exits)
        (bodyEq : ssaCcTrans body (sptInter ssaRefreshed names) nextRefreshed
                    ((ssaRefreshed, names, exits) :: tables) = (bodyOut, ssa', nextBody))
        (bodyFinalEq : (match ssaReconcile ssa' ssaRefreshed names with
                        | .skip => bodyOut | _ => bodyOut.seq (ssaReconcile ssa' ssaRefreshed names))
                       = bodyFinal) :
        (ssaCcTrans (.loop names body exits) ssa next tables).1 =
          .seq setup (.loop ssaNames bodyFinal ssaExit)

### The budget, and each input's role

| input | role | where it comes from |
| --- | --- | --- |
| setup run `(none, post)` | the `seq` evaluator's fall-through premise | the semantic side's `loopSetupCorrect` `setupRun` |
| setup charge `<= extraSetup` | the first half of the `seq` price split | the setup's own quantitative transfer / node-cost bound |
| `wordStateEqRel source post` | the loop's transfer needs a RELATE pair | the counterpart of the seq constructor's universal second IH |
| `hshape` | the compiled program | `ssaCcTrans_loop_output_shape` |
| `LoopBodyTransfer`, `LoopLocalsDomAgrees` | unchanged from the previous section | - |

Budget: `extraSetup + B * loopIterCount names body source`.  The loop's own part is still `B` per
EXECUTED iteration - no fuel, no constant factor, no new price - and the setup's charge is added
once, as a prefix, never per iteration.  Nothing is assumed twice: the run halves, the outcome
agreement and both charges are all DERIVED from `hsetup`/`hsetupCost` and `loop_quantTransfer`.

### Why not literally `ssaCcTrans_seq_quant_none`

That constructor's second IH is `forall src tgt s2 n2, quantSsaSimulation second src tgt s2 n2 tables
extra2` - universally quantified OVER STATES, which is the shape the program induction supplies but
NOT the shape of the loop constructor, whose `hinv` pins `source`/`target`.  Instantiating it would
mean assuming the loop's `quantSsaSimulation` for every state pair, i.e. assuming the conclusion.
`seq_inserted_prefix_quantTransfer` therefore performs the same accounting the `seq` constructor does
(`evaluate_seq_none`, `wec_seq_none_split_generic`, `refinedWordLocalPrice_seq_zero`, `omega`) once,
at the one reached post-setup pair, and both the loop constructor and future inserted-prefix
compositions reuse it.

### Two notes for whoever continues

1. `AllocCostSSABodyWork` CANNOT be imported here: `mergeMoves_length_le` is declared both in
   `WordOptimizerMoveCost` (pulled in by that module) and in `AllocCostReconcile` (already in this
   file's closure), so the import fails with "environment already contains".  Hence
   `ssaCcTrans_loop_output_shape` restates `ssaCcTrans_loop_output`'s first component with its own
   two-line unfolding (`simp only [ssaCcTrans, setupEq, bodyEq, namesEq, exitsEq]` then
   `split <;> simp_all`) instead of `congrArg Prod.fst`.
2. The RENAMING is still separate, and `hshape` says so: the compiled loop node keeps the SOURCE
   cutsets `names`/`exitNames`, because a loop's `quantTransfer` runs BOTH halves at the same cutset
   names (the evaluator reads `locals` by name at the cut).  Matching `.loop ssaNames bodyFinal
   ssaExit` therefore needs the source loop indexed by the renamed cutsets as well, which is the
   renaming step already flagged as remaining - not something this constructor can absorb.
