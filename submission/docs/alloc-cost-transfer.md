# Word-to-Word cost transfer: SSA, register allocation and deleting passes

This note records the checked local transfer result for the stage between
instruction selection and native lowering.  It is deliberately stated in the
new executed-work model (`InitECandidate.Runtime.FineCost.Work`), not in the old
clock/fuel model, and it never multiplies by a whole-program AST, code-table,
bitmap, ROM or `2^64`/`2^74` ceiling.

## Unit of account

`wordNodeCost` is a local syntactic envelope over a Word program: one unit per
constructor, plus one unit per word of every parallel move, plus the control
nodes.  It is not an execution count by itself.  The execution bridge is
`wordPathWork_le_nodeCost_straight`: on the straight-line fragment grammar
(`wordStraightFragment`), the work of the actually selected path of any run is
bounded by `wordNodeCost`.  The selector's own grammar is the stricter
`selectionStraightLine`, which only permits singleton moves.

The important point is that both sides are local.  A pass may add a bounded
number of nodes per rewritten instruction or per `Get`; it may not add a factor
equal to the program size, the code table, the liveness map or the number of
facts.

## Checked modules and statements

Compile order and module stems (checker role `allocation`):

1. `AllocCostModel`
   - `wordNodeCost`, `wordMoveWords`.
   - `wordPathWork_le_nodeCost` for `selectionStraightLine`.
2. `AllocCostSSA`
   - `ssaStraightOverhead` is the sum of the local instruction overheads:
     shift-with-register 3, `addCarry` 6, overflow 3, long multiply/divide 8.
   - `ssa_straight_body_cost`:
     `wordNodeCost (ssaCcTrans p ssa na lt).1 ≤ wordNodeCost p + ssaStraightOverhead p`.
   - `fullSsa_straight_cost`:
     `wordNodeCost (fullSsaCcTrans count p) ≤ wordNodeCost p + (2 + count) + ssaStraightOverhead p`.
     The `2 + count` is exactly the prologue `Seq`/`Move` pair and the `count`
     move words created by `setupSSA`.
3. `AllocCostPasses`
   - `threeToTwoReg_nodeCost`:
     `wordNodeCost (threeToTwoReg p) ≤ wordNodeCost p + 3 * threeToTwoSites p`.
     Each rewritten two-address instruction contributes one move word, its move
     node and the new sequence node.
   - `applyColour_nodeCost`: renaming preserves the envelope exactly.
   - `wordAlloc_nodeCost_le`:
     `wordNodeCost (wordAlloc ...) ≤ wordNodeCost program`.
     Both accepted oracle colourings and heuristic colourings return either the
     input or an `applyColour` image.  Spill/reload work is not hidden here; it
     belongs to the Stack/native lowering stage.
4. `AllocCostCompose`
   - `threeToTwoSites_ssa_body` / `threeToTwoSites_fullSsa`: SSA renamings and
     inserted moves create no new three-to-two sites.
   - `compiled_fragment_nodeCost`:
     `wordNodeCost (wordAlloc ... (threeToTwoRegProg enabled (fullSsaCcTrans count p)))`
     `≤ wordNodeCost p + (2 + count) + ssaStraightOverhead p + 3 * threeToTwoSites p`.
5. `AllocCostExecuted`
   - `wordStraightFragment` and `wordPathWork_le_nodeCost_straight`.
   - Preservation of the grammar through `fullSsa`, `threeToTwoReg`, `applyColour`
     and `wordAlloc`.
   - `compiled_fragment_executed`: for every actual run state, the executed
     selected-path work of the composed result is bounded by the same local
     budget.  This is an executed-path statement, not a static AST bound.
6. `AllocCostOptimizer`
   - `removeMustTerminate_nodeCost`: deleting the wrapper never increases cost.
   - `removeDead_straight_nodeCost`: dead-code removal on the straight fragment
     only drops work (filtered moves, skipped instructions, or a shorter `Seq`).
   - `copyProp_straight_nodeCost`:
     `wordNodeCost (copyProp p) ≤ wordNodeCost p + copyPropSites p`, where
     `copyPropSites` counts `Get` nodes.  A `Get` may become one singleton move,
     which costs one extra node; no other clause expands.
7. `AllocCostCse`
   - `wordCse_straight_nodeCost` and
     `wordCommonSubexpElim_straight_nodeCost`:
     `wordNodeCost (wordCommonSubexpElim p) ≤ wordNodeCost p + cseSites p`,
     where `cseSites` counts instructions, `Get`s and heap reads.  A rematerialized
     instruction becomes one singleton move, costing one extra node.
8. `AllocCostUnreach`
   - `simpSeq_straight_nodeCost` and `seqAssocRight_straight_nodeCost`.
   - `removeUnreach_straight_nodeCost`:
     `wordNodeCost (removeUnreach p) ≤ wordNodeCost p + 2`.
     The constant two is the reassociation envelope; move merging only shortens
     lists and the trailing `Skip` is deleted.

9. `AllocCostReconcile` — dynamic, per-site move budgets
   - `listNextVarRenameMove_nodeCost`:
     `wordNodeCost (listNextVarRenameMove ssa next names) = 1 + names.length`.
   - `ssaReconcile_nodeCost_le`:
     `wordNodeCost (ssaReconcile cur target names) ≤ 1 + |names|`.
     The proof bounds the reconciled move list by the live-name list, so the
     budget is the actual loop/call live set, never a whole-program maximum.
   - `loopSetup_nodeCost_le`:
     `wordNodeCost (loopSetup names exitNames ssa next) ≤ 3 + 3 * |names ∪ exitNames|`.
   - `fixInconsistencies_nodeCost_le`:
     both handler programs together cost
     `≤ 6 + 8 * |dom left ∪ dom right|`.
     This is the dynamic exception-handler budget; it counts only the actual
     union of the two branch maps.
10. `AllocCostSSAControl` — static control-flow syntax envelopes
   - `ssaCcTrans_loop_nodeCost_le`: for a loop whose body transfer
     `wordNodeCost body' ≤ wordNodeCost body + bodyBudget` has already been
     established,
     `wordNodeCost (ssaCcTrans (loop names body exitNames) ssa next lt).1`
     `≤ wordNodeCost (loop names body exitNames)`
     `  + (8 + 3 * |names ∪ exitNames| + |names| + bodyBudget)`.
     The body bound is a parameter, so this composes with any induction or
     scheduling argument instead of assuming a whole-program AST maximum.
   - `ssaCcTrans_break_target_nodeCost_le` /
     `ssaCcTrans_continue_target_nodeCost_le`: at a live loop target, the
     reconciliation move is paid from the actual exit/live name set:
     `≤ wordNodeCost (break n) + (|exitNames| + 4)` and
     `≤ wordNodeCost (continue n) + (|names| + 4)`.
     The conditional forms take the reconciled program and its exact cost bound;
     the unconditional target forms discharge them with
     `ssaReconcile_nodeCost_le`.
   - `ssaCcTrans_call_none_nodeCost_le`: a non-returning call pays only its
     argument move:
     `≤ wordNodeCost (call none dest args h) + (4 + args.length)`.
   - `ssaCcTrans_call_some_ret_nodeCost_le`: local returning-call composition
     for the return handler, with no exception handler.  It takes the actual
     stack/return move lists and the return handler budget `B` and proves
     `≤ wordNodeCost (call (some ...) ... none)`
     `  + (10 + 2 * |ls| + args.length + ret.length + B)`.
   - `ssaCcTrans_call_some_nodeCost_le`: the full returning-call composition
     with both return and exception handlers.  It takes the actual return and
     exception handler budgets and the actual `fixInconsistencies` outputs, and
     proves
     `≤ input + (24 + 3 * |ls| + args.length + ret.length + B_ret + B_exc`
     `  + 8 * |dom ssa2 ∪ dom ssa3|)`.
     No cost oracle is assumed; the handler budgets are explicit.

   These are syntactic `wordNodeCost` envelopes.  In particular the loop
   theorem counts the body syntax once; it is not an executed-cost theorem for
   repeated iterations.  The executed per-site charges are in
   `AllocCostSSAExecuted`.
11. `AllocCostSSAExecuted` — executed reconciliation charges
   - `ssaReconcile_straight` / `loopSetup_straight`: the inserted programs stay
     in the straight-line grammar.
   - `fakeMoves_straight` / `fixInconsistencies_straight`: both exception
     handler reconciliation programs are straight, so their actual execution
     is covered by the static move/fake-move grammar.
   - `ssaReconcile_executed_le`: at *every* concrete state,
     `wordPathWork (ssaReconcile cur target names) state ≤ 1 + |names|`.
     This is the actual executed charge at an exit, not a syntax count.
   - `loopSetup_executed_le`: at every concrete state, the executed setup is
     `≤ 3 + 3 * |names ∪ exitNames|`.
   - `fixInconsistencies_executed_le`: at every concrete state, both exception
     handler reconciliation programs together cost
     `≤ 6 + 8 * |dom left ∪ dom right|`.  This is the executed exception-handler
     charge, not a syntax count.
   - `loopBodyFinal_executed_le`: for one actual iteration,
     `wordPathWork (bodyFinal) state ≤ wordPathWork body state + (|names| + 2)`.
     The back-edge move is charged at the actual intermediate state of that
     iteration; the theorem is per execution and has no whole-loop maximum.
   - `exitAfterMoves_executed_le`: `break`/`continue` reconciliation is charged
     at the actual state, given the leaf exit has work one.

   - `ssaLoopExtra`: the recursive extra budget that follows the actual source
     iterations, charging `bodyBudget + backBudget` on every iteration whose
     body runs and continues.
   - `SsaLoopStep`: the explicit one-step semantic premise.  It gives the same
     source/target body result, related successor states (also after
     `decClock`), clock agreement, and one-execution body work transfer.  It is
     an original SSA-state-relation obligation, not a cost oracle.
   - `ssaLoop_executed_transfer`: by strong induction on the source clock,
     `wordPathWork (loop targetBody) t`
     `≤ wordPathWork (loop body) s + ssaLoopExtra ... s`.
     Every executed back edge is charged at its actual iteration.
   - `ssaLoop_compiled_executed_transfer`: includes the actual successful
     `loopSetup` run and its executed setup budget, covering
     `seq setup loop`, not only the inner loop.
   - `ssaLoopExtra_le_work`: the recursive extra is finite and bounded by
     `(bodyBudget + backBudget) * wordPathWork (loop body)`, because each
     executed body costs at least one work unit.  This is a dynamic bound, not
     a whole-program maximum.
   - `SsaLoopStateRel`: the original `wordStateEqRel` plus `ssaLocalsRel`;
     `ssaLoop_executed_transfer_originalRel` states the same whole-loop bound
     over that original relation.
   - `ssaLoopStep_sameBody_frame`: a concrete discharge of `SsaLoopStep` for a
     body compiled to itself, over the original `wordStateEqRel` plus actual
     cut-state agreement.
   - `ssaLoop_executed_transfer_sameBody_frame`: the corresponding whole-loop
     transfer with no one-step premise.

12. `AllocCostSSABodyWork` — quantitative base body cases
   - `wordControlCost`: an executed control-node cost for straight fragments
     that counts a parallel move as one node, matching `wordPathWork` rather
     than `wordNodeCost` (which counts move words).
   - `wordPathWork_le_controlCost_straight`: on straight fragments the actual
     executed work is bounded by this control-node cost.
   - `ssaBody_skip_executed_le`, `ssaBody_move_executed_le`,
     `ssaBody_return_executed_le`, `ssaBody_raise_executed_le`: actual
     one-execution bounds for the base SSA instruction expansions.
   - `bodySimulationRunWork_skip`, `bodySimulationRunWork_move`,
     `bodySimulationRunWork_return`, `bodySimulationRunWork_raise`: public
     quantitative analogues of the pinned private `bodySimulationRun` for the
     base instructions.  Each starts from the actual `ssaSimulation` premise,
     derives the same source/target result and `wordStateEqRel` post state, and
     proves the executed work transfer.  These are the first local cases of
     the genuinely missing quantitative body-simulation lemma.
   - `bodyWork_seq`: actual sequential control composition.  Given the real
     source and target child runs to the same successful first result and the
     two executed child-work transfers at the actual intermediate states, the
     sequential target work is bounded by the sequential source work plus the
     two child budgets.  The child budgets are the usual induction hypotheses,
     not a whole-body cost oracle.
   - `ssaCcTrans_seq_output`: the literal SSA `Seq` clause decomposes into its
     two actual child outputs and `seq`.
   - `ssaBody_seq_executed_le`: composes the two child executed-work transfers
     through the actual compiler `Seq` output.  This is the first quantitative
     control constructor.
   - `bodyWork_ite_true` / `bodyWork_ite_false`: selected-branch executed work.
     The true branch pays the actual child transfer plus its inserted
     `fixInconsistencies` reconciliation at the fixed-clock intermediate state;
     the false branch pays only the child transfer.
   - `ssaCcTrans_ite_output`: the literal SSA `Ite` clause, exposing both child
     outputs and both actual reconciliation programs.
   - `bodyWork_loopFinal`: one executed loop body.  It composes the target body
     child transfer with `loopBodyFinal_executed_le`, so the inserted back-edge
     reconciliation is paid at the actual intermediate state.
   - `ssaCcTrans_loop_output`: the literal SSA `Loop` clause, exposing the
     actual `loopSetup`, renamed body, `ssaReconcile` back-edge and final loop
     program.
   - `ssaCcTrans_call_none_output`: the literal non-returning call output at an
     arbitrary target option, exposing the inserted argument move and the
     renamed call.
   - `callNoneMoveRun`: the concrete run of that inserted `Move 1 (convArgs.zip
     names)`.  A successful run exposes the values read and the post-move
     state `setVars convArgs values target`.
   - `callNone_target_selection`: from the original `ssaLocalsRel` and
     `wordStateEqRel`, the *target* argument read returns exactly the source
     argument values, and the post-move state keeps the source code map, stack
     size and clock.  Hence the compiled call selects the same `(args1, prog,
     ss)` triple as the source call.
   - `wordPathWork_call_none_body_eq` plus the terminal unfoldings
     `wordPathWork_call_none_getVars_none`, `..._badDest`, `..._findCode_none`,
     `..._handler`, `..._clock_zero`: the actual expanded `wordPathWork` call
     definition, clause by clause.
   - `bodyWork_call_none_body`: the executed-work transfer for the entered
     callee path.  The inserted argument move is charged on its actual run, and
     the whole-call inequality is *reduced* to a transfer for the callee BODY
     program `prog` at the literal `callEnv` entry states.  The remaining
     premise is that body transfer (the recursive call obligation of a
     whole-code-map induction), not the whole-call inequality.
   - `bodyWork_call_none_badDest` / `..._findCode_none` / `..._handler` /
     `..._clock_zero` / `..._move_fails`: the terminal clock, bad-shape,
     code-lookup, handler-present and failed-move paths, each charged against
     the same `+2`.
   - `callNoneEntry_eq`: the target callee entry state is the source entry
     state with the target's stack permutation
     (`wsrEq`/`callEnv` field decomposition).  `bodyWork_call_none_related_body`
     states the same transfer with the callee premise formulated only over that
     permutation difference.
   - `callNoneMove_words` / `callNoneMove_words_args`: `wordPathWork` charges
     the inserted parallel move as one control node, while `wordMoveWords` pays
     `args.length` actually moved words.  The O(n) argument copy is therefore
     not collapsed to a constant in the native composition.

   The remaining semantic obligation is now narrower: extend the quantitative
   `bodySimulationRun` from these base instructions through the remaining
   control constructors (returning-call return/exception handlers above all),
   then instantiate the original SSA source/target cut relation.  For calls the
   residual premise is explicitly a callee-BODY transfer at the actual
   `callEnv` entry states; the whole-call inequality is no longer assumed.  The
   whole-loop induction and per-iteration charging are mechanized; no cost
   oracle is assumed.

   A concrete structural point: the original loop context carries `ssa`,
   `next` and the loop tables, and `bodySimulationRun` returns a *new*
   `nextOut`/`mapOut` relation for the body result.  A fixed-relation
   `SsaLoopStep` can therefore only be instantiated directly for bodies whose
   SSA context is invariant (for example a body compiled to itself).  The
   genuinely missing original lemma is a context-indexed one-step relation
   that threads `nextOut`/`mapOut` through the actual iteration.  The fixed
   relation above is kept because the whole-loop induction and charging are
   independent of that context threading; the base quantitative cases do not
   assume it.

All modules are checked with only `propext`, `Classical.choice` and
`Quot.sound` in their axiom closure; there is no `sorry`, `admit`, custom
axiom, `unsafe`, `native_decide` or `bv_decide`.

## What is not yet covered

- The straight-line fragments before allocation are still handled by the
  earlier theorems.  The reconciliation *budgets* for loops, `break`,
  `continue` and exception handlers are now proved in `AllocCostReconcile`, and
  the loop and call-none transfer is proved in `AllocCostSSAControl`.  The
  whole-loop induction over actual iterations is mechanized in
  `AllocCostSSALoopExecuted`.  The remaining semantic gaps are the quantitative
  `bodySimulationRun` control-constructor cases and the returning-call
  return/exception handler branches.  Base-instruction quantitative cases are
  proved in `AllocCostSSABodyWork`; the per-execution reconciliation charges,
  the return-handler local call composition and the `fixInconsistencies`
  handler budget are proved.  These are exposed as explicit premises, not
  assumed silently.
- The non-returning call work transfer is now proved from the expanded
  `wordPathWork` call clause and the original `ssaLocalsRel`/`wordStateEqRel`
  relations, reducing the residual obligation to a callee-BODY transfer at the
  literal `callEnv` entry states.  Its genuinely uncovered path is a source
  whose argument read fails while the compiled argument move still succeeds:
  the SSA locals relation is one-directional, so that failing prefix is not
  bounded by this lemma and must be handled where the source run is known to
  succeed (or by a separate reverse-direction argument).
- The returning-call work transfer is now proved from the same expanded call
  clause: `wordPathWork_call_returning_result` (source) and
  `wordPathWork_compiled_call_returning_result` (compiled `seq` of stack move,
  argument move and renamed call) decompose the call into the call node, the
  actual callee-BODY work at the literal `callEnv` entries, and the actual
  return-handler work at the literal post-call states;
  `bodyWork_call_returning_result` then bounds the compiled work by the source
  work plus the body transfer and the handler transfer (plus the four inserted
  nodes).  No whole-call cost premise is used.  The remaining returning-call
  obligation is the semantic alignment that instantiates those hypotheses from
  `ssaCcTrans` (inserted-move runs, cut-env renaming, result/pop
  correspondence); the public `returning*` lemmas provide the ingredients, and
  the exception-handler branch is stated the same way.
- `AllocCostSSATransport` starts the `PERM_STACK` work transport needed because
  the SSA relation picks the source permutation existentially: the executed
  work must be invariant under replacing the oracle and stack roots by a
  `PERM_STACK`-related variant.  Proved step lemmas: `mustTerminate` (default
  node), `.seq`, `.ite`, `.call` without return, and `.call` with a `result`
  return (body and return-handler transfers as explicit induction
  hypotheses).  Remaining: the `.loop` step, the exception branch of the
  returning call, and the termination-measure driver mirroring `swap_aux`.
  The step lemmas use `swap_aux`-style facts only through their hypotheses, so
  the driver supplies the actual sub-runs; no evaluation premise is assumed.
- `WordSimp`/`instSelect` selection is taken as the root participant's
  `selectionLeaves ≤ 2 * wordExpressionWork` bridge.  This note starts from the
  selected straight-line fragment and does not re-prove that bridge.
- The StackToLab/native instruction transfer and the final guest executed-work
  bound are separate stages.  `WordNativeInstructionCost` and
  `StackStraightLineCost` are the intended interfaces; no claim about them is
  made here.
- No final finite certificate or submission-binary statement is claimed.

## Actual returning-call alignment (`AllocCostSSACallAlignment`)

`AllocCostSSABodyWork` reduces the returning-call work bound to a transfer at
the compiled program shape, but it takes the inserted stack move, the inserted
argument move, the renamed argument read, the renamed paired cut, the renamed
bad-shape test and the code lookup as premises.  `AllocCostSSACallAlignment`
removes the SSA-side premises:

- `ssaCcTrans_call_returning_none_output`: the literal `ssaCcTrans` output for
  a returning call without an exception handler — stack rename move, argument
  move over the physical registers `2*(i+1)`, then the renamed call carrying
  the physical return registers, the renamed cut key and the return-handler
  move (ret code renaming, `ret'.zip regs`, renamed handler).
- `wordSemBadDestArgs_renameArgs`: the bad-shape test is preserved because it
  only inspects whether `dest` and the argument list are simultaneously empty.
- `wordPathWork_listNextVarRenameMove`: a stack rename move is a single
  parallel move, so it charges exactly one `wordPathWork` node.
- `ssaCallReturning_prepare_alignment`: from the public
  `returningPrepareArguments` (itself built on `returningRefreshArguments`)
  and the literal constituents, the actual compiled path is derived: both
  inserted moves run normally and charge one node each, `fixClock` of the
  normal stack-move run is the run itself, the renamed argument read returns
  the same values, the renamed paired cut exists at the renamed key, the
  bad-shape test is the source one, and both the frame and the mapped locals
  relation survive.
- `sourceCall_getVars_some_of_not_error`: a call whose actual source
  evaluation is not the `error` result cannot have a failing `getVars`, since
  the literal `evaluate` call clause answers `some .error` there.  This
  replaces any inversion of the one-directional `ssaLocalsRel`.
- `ssaBody_call_returning_executed_le`: the fresh actual returning-call bound
  on the literal compiled program, with the seven SSA-side premises above
  discharged.  What remains is callee-dependent and stated explicitly: the
  compiled code lookup at the physical return registers (`findT`, with its
  renamed cut domain `domT` and `regs.Nodup`), the callee result/pop
  correspondence at the renamed entry state (`runT`, `popT`, `locEqT`,
  `lenEqT`, `domUnionT`, `clockT`) and the two body work transfers.
  `calleeWork` *is* the pending body permutation transport (the root driver's
  `wordPathWork` transport across `PERM_STACK`-related entry states);
  `retWork` is the continuation transfer.  No whole-call inequality is
  assumed anywhere: both transfers are body-only.
- `ssaCallReturning_pop_alignment`: result/pop correspondence on the swapped
  stack.  From the source successful `popEnv` and the callee stack-swap key and
  value relations, the target stack swapped into the returned state pops
  successfully (the exact `popT` input), the two popped states are
  frame-related, and every target popped lookup is related — derived from the
  public `returningPopCutRelation`.

### Scope of the permutation driver (finding, 9a96048d1+)

`wordPathWork_permStack_variant` needs `List.Forall₂ permStack xs s.stack`.
`permStack` relates frames whose environment pair lists are *permutations of the
same pairs* (`holPerm`), so `permStack_keys_perm` shows the key multisets must
agree.  The SSA-renamed callee entry built by `returningCalleeTransport` pushes
`applyNummapsKey (optionLookup mapOut)`-renamed cut environments, whose frame
contents differ, so the two entries are **not** `permStack`-related (witness:
`not_permStack_singleton_rename`).  Consequently the callee body transfer is
discharged by the driver only in the stack-permutation case
(`calleeWork_permStack_zero`, `ssaBody_call_returning_no_body_oracle`, body
budget zero); the SSA-renamed case must be discharged by the callee induction
hypothesis at the related entry environments, which is what
`returningCalleeTransport`/`returningPrepareArguments` expose as
`strongLocalsRel` on the cut environments.

### Which theorem to use for the final assembly

Use `ssaBody_call_returning_executed_le` (the parametric-budget one): its
`calleeWork` premise with additive `calleeBudget` is exactly the shape of the
recursive induction hypothesis for the callee program, so the pass-level
induction plugs straight in and no whole-call cost transfer is assumed.  The
zero-budget variant `ssaBody_call_returning_no_body_oracle` remains useful only
as the stack-permutation sub-case documented above.

## Executed-cost inspection: fine model (`AllocCostSSAStackSwapWork`)

The stage above is stated in `wordPathWork`.  The fine executed model
`InitECandidate.Runtime.FineCost.wordExecutionCost` (per-node price, real
`MustTerminate` body cost) now carries the same kind of local invariance, with
no whole-budget hypothesis:

- `wec_stack_variant_dispatch`: for an arbitrary price and *only* the explicit
  local price hypothesis `hprice` (`price q {t with stack := ys} = price q t`
  for value-equal stacks), every program satisfies
  `wordExecutionCost price p {s with stack := xs} = wordExecutionCost price p s`
  from a value-equal stack and a top-level non-error hypothesis.  All
  constructors are covered, including `MustTerminate` (body charged at the reset
  clock and decremented term depth, with the body non-error transported), `seq`
  at the reached middle state, `ite`, `loop` (cut state, body and stop tail) and
  the full `call` clause.
- `wordCallReturned_stack`: the concrete `loopWordPrice` is state dependent only
  through `wordCallReturned`; its callee `.result` witness is preserved by a
  value-equal stack swap (`sValEq` symmetry, `decClock`/`pushEnv`/`callEnv`
  entry transport, result location/values/arity), so the price itself is
  invariant.
- `wordExecutionCost_loopWordPrice_stack_variant`: the actual model theorem for
  `loopWordPrice`, including the corrected returning-call price
  `1 + |args| + (returned arity when the callee returns that many values)`.
- Downstream transfer shapes consumed by the allocation call stage:
  `wordExecutionCost_callBody_transfer` (callee body cost at the stack-swapped
  `callEnv`/`pushEnv`/`decClock` entry equals the source entry cost — the
  `calleeWork` obligation) and `wordExecutionCost_returnContinuation_transfer`
  (the return-handler continuation cost on an `sValEq`-valued popped target
  stack).

These are executed-cost statements at the actual reached states; no AST,
code-table or bitmap multiplier appears, and the axiom closure stays
`propext`, `Classical.choice`, `Quot.sound`.
