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
