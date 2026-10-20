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
10. `AllocCostSSAControl` — control-flow transfer
   - `ssaCcTrans_loop_nodeCost_le`: for a loop whose body transfer
     `wordNodeCost body' ≤ wordNodeCost body + bodyBudget` has already been
     established,
     `wordNodeCost (ssaCcTrans (loop names body exitNames) ssa next lt).1`
     `≤ wordNodeCost (loop names body exitNames)`
     `  + (8 + 3 * |names ∪ exitNames| + |names| + bodyBudget)`.
     The body bound is a parameter, so this composes with any induction or
     scheduling argument instead of assuming a whole-program AST maximum.
   - `ssaCcTrans_call_none_nodeCost_le`: a non-returning call pays only its
     argument move:
     `≤ wordNodeCost (call none dest args h) + (4 + args.length)`.

All modules are checked with only `propext`, `Classical.choice` and
`Quot.sound` in their axiom closure; there is no `sorry`, `admit`, custom
axiom, `unsafe`, `native_decide` or `bv_decide`.

## What is not yet covered

- The straight-line fragments before allocation are still handled by the
  earlier theorems.  The reconciliation *budgets* for loops, `break`,
  `continue` and exception handlers are now proved in `AllocCostReconcile`, and
  the loop and call-none transfer is proved in `AllocCostSSAControl`.  The
  remaining recursive cases are the `break`/`continue` branch-cost wiring and
  the returning-call (`call some`) handler composition, where the return and
  exception handler programs and their `fixInconsistencies` budget must be
  threaded through the same symbolic state.  Those are the next missing chunk,
  not consequences of the present theorems.
- `WordSimp`/`instSelect` selection is taken as the root participant's
  `selectionLeaves ≤ 2 * wordExpressionWork` bridge.  This note starts from the
  selected straight-line fragment and does not re-prove that bridge.
- The StackToLab/native instruction transfer and the final guest executed-work
  bound are separate stages.  `WordNativeInstructionCost` and
  `StackStraightLineCost` are the intended interfaces; no claim about them is
  made here.
- No final finite certificate or submission-binary statement is claimed.
