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
