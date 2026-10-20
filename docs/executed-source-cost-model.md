# Executed Pancake work

This participant-only instrumentation leaves challenge semantics unchanged. Its
purpose is a small-coefficient native bound within the working 900,000,000,000
step ceiling. The existing Pancake call/loop clock remains a termination index;
it is not the work metric.

## Accounting rules

A source execution records statement-entry events and expression-evaluation
events, with the state, result and operation size relevant to each event.
Charge one dispatch unit per executed statement and one per executed expression.
Charge the child expression events separately. Sequence and conditional entry
are charged, but an unvisited branch contributes zero. Loop guards are charged
on every evaluation, including the final false guard. Calls charge argument
evaluation, actual argument/result words, frame setup and the executed callee;
never charge the entire callee syntax at every call in addition to its trace.
Return, break, continue, exception handlers, failing operations and resource
rejection retain their actually executed prefixes. A failed expression must not
be assigned zero merely because it produced no value.

The unit vector records distinct work classes rather than immediately assigning
unproved native coefficients. A certified backend table will turn the vector
into a scalar by a dot product. This permits distinct coefficients for scalar
arithmetic, memory, control and bulk transfer without a product of global maxima.

| Event | Additional size charge (beyond entry and child events) |
| --- | --- |
| Scalar literal, address constant, scalar variable | One scalar word produced or moved |
| Fixed-width arithmetic/comparison/shift | Number of scalar operations actually emitted; 64-bit width, not the integer magnitude |
| Variadic arithmetic | Number of reduction operations over evaluated operands |
| Structured variable/copy/assignment/argument/return | Actual flattened words moved |
| Structured construction | Actual flattened output words, plus field bookkeeping where compiled |
| Field projection | Selected flattened words and emitted address/index work |
| Structured load/store | Actual scalar memory accesses required by the flattened shape |
| Byte/32-bit access | Actual access expansion, including alignment-dependent split accesses |
| Function frame | Actual saved/restored registers, stack slots and argument/result moves |
| External/shared-memory operation | Setup and native event steps, plus bytes/words processed by any guest-side transfer loop |
| Hashing/bulk primitive | Actual input blocks, bytes or words handled by guest implementation, plus fixed setup/finalization |

For accelerator/MMIO operations, distinguish one native event from any guest
copying/packing: host computation is charged only if the authoritative runtime
counts it. No universal per-byte host charge is assumed. A hashmap receives no
constant-time allowance: its executed probe/traversal events and key comparisons
are charged, preserving quadratic worst cases when present.

## Proof obligations

1. Instrumented expression evaluation erases to exact expression semantics,
   including failures and precisely the evaluation order used by that semantics.
2. Instrumented statements erase to exact finite-state semantics, with complete
   rules for declarations, loops, calls, handlers, FFI and terminal outcomes.
3. Local compiler simulation bounds native execution by the corresponding work
   vector, accounting for register allocation, spills and target expansions.
4. Compose local simulations additively, including initialization and terminal
   overhead. Avoid multiplying maxima from every pass over the whole program.
5. Bound the resulting work vector from input size, consumed challenge gas and
   algorithm invariants. Compute the final scalar score and verify it end to end.

Current implementation: `PanWorkVector` records typed work events and proves
additive scalarization. `PanExpressionWork` has exact rules for constants,
variables, comparisons, shifts, binary arithmetic, record projection, and byte/32-bit
loads (including missing address results). `PanStatementWork` connects guard
expression events to sequence and conditional execution. These remain partial:
full expression/statement coverage and completeness are not proved. The memory
counter currently counts logical scalar reads; its eventual native coefficient
must cover the alignment and width expansions of all admitted scalar reads.
Structured stores charge the flattened request word count; rejected stores
conservatively charge the entire request, which bounds any shorter attempted
prefix. Scalar byte/32-bit stores charge one logical access. The native memory
coefficient must cover both reads and writes. Structured load rules remain open.
Statement rules also cover loop control, assignments, returns and successful
exception payloads; these do not yet give full statement completeness. `LabLocalWork`,
`LabWeightedInstructionTrace` and `LabWeightedMixedTrace` prove local native
bounds at the label backend. They do not yet establish the source work vector
or a complete finite certificate. Native coefficients in the table above remain
to be certified; the size charges specify the accounting policy, not assumed
compiler theorems.

## Compiler-induced repeated work

`PanToCrep.compileExpExactHOLW` lowers a structured load using
`loadShapeBytesHOLW`: every result word contains another copy of the compiled
address expression. Source evaluation computes that address once. The source
cost rule therefore needs a size-dependent replay allowance, in addition to
its actual expression events and memory-word charge. Nested structured loads
must compose this allowance recursively; a universal one-word charge is not
sufficient.

`CrepExpressionWork.loadShape_work_bound` proves, for the actual pinned
flattening helper, that the sum of emitted scalar expression nodes is at most
`words * (addressNodeWork + 3)`. The three extra nodes cover a load, offset
addition and offset constant. This bound is independent of whole-program size.
It is a syntactic expansion bound, not yet a native runtime theorem. Field
projection can discard some expanded expressions, so this full-load bound is
conservative for a projected load. The expression/source cost connection must
retain these local multiplicities rather than assume flattening is free.

`PanLoweringAllowance.pan_lowering_work_bound` now assembles these local
inequalities for every expression constructor of the exact Pan-to-Crep pass.
Its allowance uses the current compiler context's local variable word counts,
sums record/operand allowances, and multiplies structured load address work by
the load's word count. It does not depend on whole-program syntax size.
Named structures and globals still take the literal fallback clauses at this
pass: correctness and cost of their earlier preprocessing must be connected
separately. This theorem bounds generated expression nodes; execution-frequency
accounting and the later compiler/runtime transfer remain open.

`CrepToLoopLocalBound` proves a coefficient-six bound for every scalar Crep
expression, covering both emitted straight-line code and the residual Loop
expression. Its list theorem also reserves one unit per result for argument
materialization, so nested variadic operations compose without another global
multiplier. Conditional materialization charges the larger branch allowance.
The partial code-work function rejects loops/calls rather than silently giving
them a static cost. `pan_to_loop_expression_work` composes this theorem with
the Pan-to-Crep allowance, retaining coefficient six. These are generated-work
bounds, not yet an executed trace or RISC-V runtime bound; instruction selection,
register allocation, later lowering, and execution-frequency proofs remain.

`LoopExecutedWork` now defines exact evaluator traces for the expression-code
subset and proves soundness, allowance boundedness and completeness for every
program accepted by the code-work function. Sequence traces stop on a terminal
result; conditionals trace only their selected child, apply the exact `cutRes`,
and include missing/nonword guard errors. Atom charges conservatively include
full residual expression allowances, including when evaluation fails early.
`compiled_pan_expression_trace` combines this completeness result with the
coefficient-six theorem, so the allowance bounds an actual evaluator trace,
with residual value work reserved for the enclosing statement. It remains a
Loop work bound rather than a count of compiled RISC-V steps.

`PanTotalExpressionCost` replaces reliance on the partial expression trace for
statement accounting. It defines work for every exact Pancake expression,
including named structure guards, field operations, arbitrary argument lists,
structured loads and malformed/missing results. `CostedExpressionRun` pairs the
exact evaluator result with this canonical event list and is total without
success or syntax assumptions. `PanStatementWork` now uses that relation.
Expression lists retain all children of the exact evaluator's pair-matched list
clauses. Structured loads charge requested words even on memory rejection and
actual output words for copying; failed prechecks skip guarded children.
Every attempted expression pays its entry cost. The source-cost scalarization
is still parameterized: its relation to the compiler-aware lowering allowance,
full statement coverage and native coefficients remain proof obligations.

Ordinary call rules now expose argument evaluation, callee execution, terminal
exit dispatch and any matched handler execution. `PanCallCostPlan` proves that
pure dispatch exactly matches the authoritative call clause, including return
shape/assignment checks, exception identity/shape checks and all fallback
results. Statement traces charge actual argument words, argument slots and
returned/exception payload words. Lookup/argument failure and clock exhaustion
have separate prefixes. The successful `DecCall` rule also includes its
continuation and binding restoration. Other `DecCall` outcomes, FFI/shared
memory/primitive clauses, malformed-control cases and whole-statement
completeness remain open. Compiler-generated frame/spill costs still require
layout-sensitive bounds beyond these source argument-slot events.

Declared-call failure/timeout, rejected returns and non-return terminal outcomes
now have source cost rules. Malformed conditional/loop guards, malformed store
addresses and narrow-store values, rejected/undeclared exception payloads,
ticks, annotations and all primitive operation outcomes are also covered by
the checked soundness theorem. This expands constructor/outcome coverage; it
does not yet establish whole-statement completeness. External/shared-memory
operations and that completeness proof are still outstanding.

`PanExternalCost` supplies canonical external/shared-memory event lists.
External input attempts charge requested bytes; successful reads permit a native
event, and returning calls charge actual returned bytes. Shared operations use
a conservative one-event allowance after operand checks, even if a subsequent
domain/oracle guard rejects them. Native width-specific expansion bounds are
still required. Statement rules expose these three nonrecursive atomic semantic
boundaries with exact evaluator results; no callee/loop/handler body can use
these rules. The statement relation now has rules for every source constructor,
but its global completeness theorem remains to be proved, followed by the
compiler cost relation, guest cost bound and end-to-end score verification.

## Global source completeness

`PanCostTotal.source_statement_cost_complete` now proves cost-trace existence
for every exact source state/program, without successful evaluation or guest
well-formedness assumptions. Its well-founded measure is `(source clock,
program size)`: calls/loop iterations decrease clock, structural composition
uses clock monotonicity and a smaller program, and handler/continuation entry
preserves the callee's remaining clock. All proof axioms are standard Lean
`propext`, `Classical.choice` and `Quot.sound`.

`sourceExecutionEvents` selects a certified finite trace;
`sourceExecutionCost` scalarizes it with the coefficient vector.
`sourceExecutionCost_spec` connects that function to exact evaluator outcomes.
No trace uniqueness theorem is claimed: compiler and guest bounds should be
proved for every trace, which also covers the selected witness. This completes
global existence for the source cost definition, not the native transfer or
any numerical bound on guest cost. Native frame/spill/replay charges and the
connection to the compiler-aware allowance still need to be certified before
choosing final coefficients and claiming a score.
