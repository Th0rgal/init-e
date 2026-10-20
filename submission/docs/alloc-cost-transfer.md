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

   The remaining semantic obligation is now narrower: extend the quantitative
   `bodySimulationRun` from these base instructions through the control
   constructors, then instantiate the original SSA source/target cut relation.
   The whole-loop induction and per-iteration charging are mechanized; no
   cost oracle is assumed.

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
  `bodySimulationRun` control-constructor cases and the exception-handler
  branch of the returning call.  Base-instruction quantitative cases are
  proved in `AllocCostSSABodyWork`; the per-execution reconciliation charges,
  the return-handler local call composition and the `fixInconsistencies`
  handler budget are proved.  These are exposed as explicit premises, not
  assumed silently.
- `WordSimp`/`instSelect` selection is taken as the root participant's
  `selectionLeaves ≤ 2 * wordExpressionWork` bridge.  This note starts from the
  selected straight-line fragment and does not re-prove that bridge.
- The StackToLab/native instruction transfer and the final guest executed-work
  bound are separate stages.  `WordNativeInstructionCost` and
  `StackStraightLineCost` are the intended interfaces; no claim about them is
  made here.
- No final finite certificate or submission-binary statement is claimed.
