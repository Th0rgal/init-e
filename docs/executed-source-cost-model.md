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

`PanScalarCostTransfer` connects source expression costs to the compiler-aware
allowance for scalar loads/operations and record composition. Its source vector
charges four units per expression entry and one per moved word; it is an
intermediate vector, not the final native coefficients. `LocalWidthsFit` states
an explicit context/runtime-width invariant and still needs to be derived from
the compiler state relation at guest entry and preserved layouts. The resulting
`scalar_source_to_loop_cost` theorem bounds actual generated Loop traces by six
times source expression cost, including residual values. General multiword loads
are excluded by `scalarLowering` because address replay needs separate accounting.
Preprocessing and subsequent native lowering remain outside this theorem.

`PanLayoutCost.related_local_width` derives exact slot/runtime-word equality
from the pinned `panToCrepLocalsRelFiniteExact` for a present source variable.
`related_local_source_to_loop_cost` consequently discharges the layout condition
for successful local reads, without whole-context coverage. The compiler locals
relation is one-way and permits additional context entries, so it cannot imply
`LocalWidthsFit` universally. A separate coverage lemma records the missing
domain premise explicitly. Compound-expression transfer should instead exploit
successful evaluation to establish presence of the variables actually read;
this refinement remains open, alongside later native lowering and the guest bound.

The scalar transfer is now generalized in `PanScopedCostTransfer` to require
widths only on `varExpHOL expression`. The previous whole-context theorem is a
short wrapper; shared definitions live in `PanScalarCostModel`, avoiding two
copies of the structural proof. `PanLayoutCost.related_scalar_source_to_loop_cost`
combines this scoped result with the compiler locals relation and presence of
the read variables. Extra uninitialized context entries impose no obligation.
Deriving read-variable presence directly from successful expression evaluation
remains the next refinement; the RISC-V and guest-bound obligations are unchanged.

`PanReadPresence` now proves that successful exact expression evaluation implies
presence of every name in `varExpHOL`, covering all constructors and both list
helpers. `PanLayoutCost.successful_scalar_source_to_loop_cost` uses this fact
to eliminate the independent read-presence premise: successful evaluation and
the existing compiler locals relation suffice for the scalar source-to-Loop
work bound. This still excludes general multiword loads and does not yet cover
later RISC-V lowering, source statement transfer or the guest's numerical cost.

A text audit of the pinned `Guest/Ast.lean` found 1,290 one-word loads,
247 flat four-word loads and 62 flat six-word loads. This is a source inspection,
not yet a kernel certificate that every address satisfies the scalar predicate.
`PanBulkLoadCost` proves the local transfer for successful loads of at most six
words whose addresses satisfy that predicate. It derives address layout and
shape validity from successful evaluation plus the compiler locals relation,
and bounds generated Loop trace work by 36 times source expression cost. This
covers address replay locally without a whole-program syntax multiplier.
Compound expressions containing such loads, guest-wide applicability and later
RISC-V lowering still require proofs.

`PanBulkExpressionCost` extends the local allowance proof through arbitrary
compound expressions whose multiword loads have scalar addresses, width at
most six, and valid shapes. The additional factor stays six over the whole
expression rather than multiplying at each surrounding node.
`GuestBulkLoadSites.guest_bulk_load_sites` is now a kernel `decide_cbv`
certificate traversing every pinned guest function/global initializer, including
call handlers and all expression children. It confirms the size/scalar-address/
empty-context-shape pattern at every load site. `GuestBulkLoadApplicability`
lifts that static predicate to all source structure contexts and proves the
compound source-to-Loop execution bound with coefficient 36. This does not
establish compiler-artifact agreement, statement execution counts, native
RISC-V transfer or the final guest score.

`LoopToWordExpressionWork` proves exact preservation of expression work through
the pinned Loop-to-Word compiler. `topAddr` is charged five nodes locally for
its heap-base/length expansion; all other nodes preserve their structure.
`LoopToWordCodeWork` proves exact preservation of the expression-code allowance,
including the tick emitted after a conditional. Loop conditional work is now
two units plus the larger branch allowance. The Crep-to-Loop coefficient-six
proof, executed traces, source expression transfers and guest kernel certificate
were rebuilt successfully with these calibrated charges.
`LoopToWordValueCost` pairs the work equality with the existing exact value
simulation on the same compiler output. Word expression instruction selection,
register allocation/spills and later native lowering are still outstanding;
these equalities do not constitute an end-to-end RISC-V runtime bound.

`WordFlattenWork` proves `work(flattenExp e) + 1 ≤ 2 * work(e)` for every Word
expression, with a list potential that makes binary normalization compose.
`WordSelectionWork.raw_selection_work_bound` proves that the raw pinned
instruction selector emits at most one selected leaf per input expression node.
`flattened_selection_work_bound` combines these bounds without a program-size
maximum. These are counts of emitted selector leaves, not RISC-V runtime steps.
The full selector first applies `pullExp`; its work bound, selected-code execution
simulation, register allocation/spills and subsequent native passes remain open.

`WordPullWork.pull_expression_work` now proves nonamplification for the actual
constant-pulling function, including subtraction conversion, associative
operand pulling, partitioning and constant reduction. It uses the pinned
executable/original agreement theorem and only standard Lean axioms.
`assignment_selection_work_bound` consequently covers the full pinned assignment
selector, with `selectedLeaves + 1 ≤ 2 * expressionWork`, including pulling and
binary normalization. The Loop-expression version composes with exact work
preservation through Loop-to-Word. Selected-code runtime simulation, allocation/
spills and later native transfer remain separate unfinished obligations.

`WordSelectionStraightLine` certifies that every raw selector output consists
only of supported straight-line leaves and sequences. Skips count as one leaf,
matching the conservative execution budget. `WordSelectedPathCost` proves
`wordPathWork p state + 1 ≤ 2 * selectedLeaves p` for this grammar, following
actual successor states and allowing early termination. The full preprocessed
assignment therefore has selected-path work at most `4 * expressionWork`.
`WordSelectedStackCost` retains the full pinned Word-to-Stack simulation
premises and resource/result postconditions with that same budget for additional
Stack clock. This is not yet a RISC-V instruction bound: allocation/spill costs
and the remaining native transfer must still be composed.

`StackStraightLineCost` bounds actual selected Stack-to-label path work by
`4 * stackLeaves - 2` for certified straight-line fragments, including early
exits. `WordNativeInstructionCost` proves each pinned native integer instruction
lowering is such a fragment with at most four leaves (two reloads, an operation,
and a spilled write), so its path budget is at most 14. The coefficient is
independent of total frame/code size. All HolInst constructors are covered;
this is still local to instruction lowering, not a bound for allocator-added
moves, full selected expressions, or final RISC-V execution.

`WordNativeMoveCost` proves singleton scheduling introduces no temporary and
lowers to at most two Stack leaves. `WordSelectionNativeCost` covers all selected
straight-line output: at most four Stack leaves per Word leaf, with actual
Stack-to-label path budget at most 32 times Word/Loop expression work. Its
flattening theorem retains original premises. Word allocation/optimization and
Stack removal remain separate stages; this is not an end-to-end native claim.

`StackAddressCost` bounds the literal up/downshift recursions by
`addressChunks slots = slots / 255 + 1`. `StackRemovalLocalCost` counts each
actual spill offset: a direct encodable offset costs one instruction; otherwise
a load costs at most `addressChunks slots + 2` and a store at most
`2 * addressChunks slots + 1`, including pointer restoration. Certified
straight-line removal outputs have actual label-path budget at most four times
this sum, and the full flattening simulation retains that bound. No global
frame/code/bitmap multiplier is introduced.

## Return-slot frame epoch

Compiled calls with return metadata and declared calls zero-initialize their
return slots before entering the callee, even when the callee then times out
or raises. Source call rules therefore charge `frame (size of return shape)`
after a successful callee lookup: `callDone`, `callHandler` and `callTimeout`
use the looked-up callee return shape; `declareCallReturn`,
`declareCallRejectedReturn`, `declareCallStopped` and `declareCallTimeout` use
the declared shape. Argument and lookup failures are unchanged. Calls whose
compiled form allocates no slots are conservatively over-charged. This
replaces the earlier static return-size premise of the Crep transfer and lets
its statement coefficient stay small; trace existence proofs are unchanged.

## Source-to-Crep executed transfer

`SourceCostCrepWork.CrepWork t p w` counts executed Crep work: one unit per
executed statement and the scalar node work of every evaluated expression,
following the exact evaluator's successor states (selected branch, every loop
guard, actual callee body, matched handler, early failures). Calls also charge
argument words and returned payload words. `SourceCostCrepControl.source_crep_executed_work`
proves, for every exact source `StatementRun` with a non-error result, the four
original `pc_compile_correct` relations, `localised_prog`, and the guest
load-site certificate on the program and every function body, that the
compiled Crep execution has a `CrepWork` derivation bounded by
`sourceCrepWeights.score` of the source event vector, with weights statement 8,
expression 24, moved word 8, memory access 8, frame slot 8. All source
constructors are covered, including declarations, structured assignment and
stores through fresh temporaries, calls with return slots, caught handlers,
declared calls, primitives, FFI and shared memory. No whole-program size enters
the bound. `source_execution_cost_pays_crep` restates it for the selected
canonical trace.

## Seq-free epoch

`Seq` is structural composition with no native operation, so it emits no
event of its own. `StatementRun.seqNext` charges `left ++ right` and `seqStop`
charges `left`. `CrepWork` `Seq` likewise has no local charge (`w1 + w2`, `w1`).
Every executable statement, expression, loop guard, call and size event is
still charged. Without this change, `pan_simp$seq_assoc`, which left-nests
sequences, would pay one extra `Seq` statement per enclosing sequence node on
every early exit. That is a program-size factor. With `Seq` free, association
never changes cost (`SourceCostPanSimpAssoc.simp_seqAssoc_run`).

## Crep-to-Loop executed transfer

`SourceCostLoopWork.LoopWork s p out w` counts executed Loop work rule by rule
on the exact Loop evaluator (leaf costs, selected branches, every loop
iteration, actual callee bodies, return-slot copies, handler dispatch, short
calls). `SourceCostLoopControl.crep_loop_executed_work` proves by induction
on `CrepWork` that every Crep execution with a non-error result and the
original `ncompile_correct` relations has, at some clock extension of the
Loop state, a `LoopWork` derivation of the compiled `compileHOLExact` code
bounded by `7 *` the Crep work, together with all original `ncompile_correct`
conclusions (`LoopPaid`). All Crep constructors are covered with no static
coverage premise. Clock extensions are composed explicitly. Work is lifted
to a larger clock only on non-timeout prefixes (`LoopWork.add_clock`). The
factor is 7, not 6, because a call that times out at clock zero pays Crep
`1 + crepListWork args`, while its compiled code also moves each argument
(`<= 6 * crepListWork + 1 + |args|`).

The call case (`SourceCostLoopCall.call_loop_paid`) takes the named contract
`SourceCostLoopCallBase.LoopOptimiseWork`. Root discharges it with
`loop_optimise_executed_work` (coefficient one), via
`SourceCostLoopSource.loop_optimise_work`. `crep_loop_installed_work` and
`source_simp_loop_installed_work` are therefore unconditional. The contract says
that the per-function `optimiseHOL` pass does not increase executed work for
non-error, non-break and non-continue results.
`SourceCostLoopSource.source_loop_executed_work` composes the two transfers
for one statement.

`SourceCostCrepSimp.crep_simp_work` transfers `CrepWork` across
`crep_arith$simp_prog`. The transfer never increases work, needs no clock
extension, and holds for every non-error run. It uses the pinned lockstep
`crepArithSimpProgCorrect` and the fact that `simp_exp` never increases node
work (`crepSimp_node_work`). `source_simp_loop_executed_work` composes all
three passes for one statement: source → `pan_to_crep` → `simp_prog` →
`crep_to_loop` compile. It runs against the `simp_prog`-mapped Crep state,
which is how `compile_prog` installs function bodies. 
`pan_simp` statement transforms are covered for the same code map.
`simp_seqAssoc_run` handles `seq_assoc` on every run, and `simp_retToTail_run`
handles `ret_to_tail` on non-error runs. Under every coefficient vector, the
work is no more than the source run's.

`SourceCostPanSimpCode.simp_compile_run` transports runs across the
`pan_simp` code map, and `SourceCostSharpPanSimp.simp_compile_run_sharp`
gives the sharp-score corollary. `SourceCostPanStructsId.compileTop_structFree`
shows that `pan_structs` is the identity on struct-free programs, and
`SourceCostCrepInlineId.compileProgDecls_noInline` shows that `crep_inline` is
the identity when there are no `inline` declarations.

## Global-access epoch

`pan_globals` turns a global variable into a memory access off `TopAddr`.
For a global of `n` words:

- A read becomes `Load shape (Op Sub [TopAddr, Const a])`.
- An assignment becomes the matching `Store`.
- A call result stored into a global becomes a `DecCall` into a temporary,
  followed by that `Store`.

The canonical trace records these accesses with a dedicated event,
`WorkEvent.globalAccess n`. Its units are `{globalAccesses := 1, globalWords
:= n}`. The event is emitted, in addition to the ordinary copy, by:

- a global read (`expressionEvents`, through `globalEvents kind`);
- a successful global assignment (`assignValue`);
- a call into a global destination (`callGlobalEvents`), sized by the global's
  current value and charged whenever the call is entered (`callDone` and
  `callTimeout`). `pan_globals` declares a temporary of the global's shape around
  such a call, so its frame is paid on exception and timeout exits too.

Local variables emit no extra event, and the prices of all existing events are
unchanged. `replayUnits` counts `k - 1` for `globalAccess k` as well as for
`memory k`.

The sharp coefficients are `globalAccesses 40` and `globalWords 17`, plus the
replay term. A one-word global access therefore costs 57, and an `n`-word
access costs `40 + 17n + 45(n-1)`. This is the largest expansion of the three
cases under the sharp score:

| Case | Expansion cost |
|---|---|
| Read | `25 + 12n + 45(n-1)` |
| Assignment | `25 + 7n + 45(n-1)` |
| Call result into a global | `40 + 17n + 45(n-1)` |

In every case the address `Op Sub [TopAddr, Const a]` has Loop price 10,
which is within the replay certificate of 40.

`SourceCostGlobalsRun.globals_compile_run` is the `pan_globals` run transfer.
It holds for every replay bound `B`. Given a non-error source run and the
original `compile_correct` relation, the compiled program has a canonical run
that:

- has the same result;
- ends in a state related by `compile_correct`;
- has `sharpSourceScore B` at most the source run's.

It assumes the following of the program and the state:

- `globalsReadyProg` holds of the program.
- `GlobalsCodeReady` holds of the code map: every installed body is ready, and
  no parameter is named like the temporary.
- The start state has no local named like the call temporary `""`.
- `GlobalsCovered` holds: every laid-out global is present in the source state.

The run invariants `StatementRun.code_eq`, `StatementRun.noTemp` and
`StatementRun.globals_present` keep these assumptions true along the run.

## Sharp replay sites

A `k`-word structured load evaluates its compiled address list once. It then
re-evaluates only the list's head for each further word, at Loop price
`crepHead + 6` per word (`sharp_compiled_load`). The site certificate
`sharpSites B` asks every multiword load address to be in the `headAddr`
grammar with `sharpHeadPrice address + 1 ≤ B`:

- The grammar admits scalar operators, constants, `BaseAddr`/`TopAddr`, nested
  loads, locals and record fields of locals.
- A record field of a local compiles to one selected variable, so its head
  costs 2 (`localTree_small`).

`SourceCostSharpHead.head_bound` shows the compiled head costs at most
`sharpHeadPrice`, syntactically and for every context. It needs no layout or
value hypothesis.

## Installed entry

`SourceCostEntry.entry_loop_sharp_work` composes the transfers for the
installed whole program fed to `pan_to_crep`. It starts from the initial states
of the pinned `state_rel_imp_semantics` theorems: the `pan_to_crep` top-level
relation with installed code, and the `crep_to_loop` relation with
`compile_prog` of the `crep_arith`-simplified bodies.

It states that the source run of `Call NONE start []` at any clock is matched
by the installed Loop entry, whose `LoopWork` is at most `sharpScore` of the
same canonical source events.

The static premises are:

- no inline declarations;
- localised bodies;
- the site certificate on every installed body;
- the pinned premises of both semantics theorems;
- the `start` lookup.

For the guest, `GuestCostSharpSites` certifies the sites on `pass2`.

## Whole-program preprocessing

`SourceCostSourceTop.source_top_entry` starts from the original entry run
`Call NONE start []` in the post-declaration state of the original program, at
any clock. It ends with the run of the generated entry of the program
`pan_to_crep` receives, from the state the target declarations produce, at one
more clock tick. The generated entry's events cost at most the original's
under `sharpScore`, plus a one-time
`globalsTopInit = 20 + 4·|return shape| + 57·#globals + 5·payload`.

The steps are:

1. `pan_simp`: `simp_top_entry`, via the pinned `evaluateDeclsCodeRel` and
   `simp_code_run`.
2. `pan_structs`: the identity on struct-free programs.
3. `pan_globals`: `globals_top_entry`, which follows the pinned
   `compile_top_semantics_decls` proof at run level.

`globals_top_entry` uses four lemmas:

- `fperm_run`: renaming functions keeps events exactly.
- `entry_empty_locals`: the entry call does not read the caller's locals.
- `globals_inits_score`: each constant global initialiser costs 57.
- `globals_run_le`: covers the renamed original entry.

`decls_clock` shows that declaration evaluation does not depend on the clock.

`SourceCostLoopTop.source_loop_top` is the end-to-end statement. It takes the
original entry run from the post-declaration state of the original declarations,
at any clock. The installed Loop entry of the compiled program then has, after a
clock extension, `LoopWork` at most `sharpScore` of the original events plus
`globalsTopInit`. The original `LoopRunRel` conclusion is kept.

The per-state pipeline premises (`EntryPipeline`) are those of the pinned
`pan_to_crep` and `crep_to_loop` `state_rel_imp_semantics` theorems. They are
stated for the actual post-declaration state of the compiled program.

`SourceCostInitial.source_loop_initial` instantiates this at the initial states
of the pinned `panToWordStateRelImpSemantics` proof:

- the `pan_globals` target state;
- `crepStateHOL`;
- `loopStateHOL`, built from the source state and the Word target state.

It derives every `EntryPipeline` field from that theorem's premises, following
its own proof. The remaining premises are static facts about the program:

- no structures;
- no inline functions;
- the replay-site certificate;
- `pan_globals` readiness;
- constant global initialisers;
- the parameterless `start` function.

For the guest, these are certified on the exact compiler stages.

## Guest instantiation

`GuestCostSourceLoopTop.guest_source_loop` is the guest statement. It starts
from `sourceInitialState input` and the authoritative declaration evaluation
of `Guest.guestAst.map declToHOL`. The `main` run starts from the resulting
state, at any clock, and must not end in an error. Three Word-side facts stay
explicit hypotheses:

- `hmem`: memory agreement;
- `hnolabels`: no labels in the target memory;
- `hmdomain`: the domain equation.

The conclusion bounds the installed Loop entry's `LoopWork` by
`sharpScore ev + 5330`.

The proof proceeds as follows:

- `original_declaration_evaluation` moves from the original declarations to
  the main-first `sourceDeclarations` that the compiler receives.
- The static premises are certified on `pass0` and `pass2`.
- The one-time Init is 5330 = 20 + 4·1 + 57·93 + 5·1:
  - `main` returns one word;
  - the generated entry has 93 constant global stores;
  - the payload is at most one word, from `guest_entry_payload`.
- The payload bound comes from `GuestCostEntryShapes`. It certifies that every
  `main` entry returns one well-formed word and that every declared exception
  carries one.

## Loop to Word

`LoopWordCost.loop_to_word_cost` is the transfer theorem. It applies to every
`LoopWork` run and every Word state related to the Loop state as in the
pinned `loop_to_word` `compile_correct`. It bounds the executed Word work of
`compHOL ctxt p l` under `wordExecutionCost loopWordPrice` by the `LoopWork`
of the same run, with coefficient 1. The proof is an induction on `LoopWork`.
The pinned `compileCorrect` supplies the Word successor states, and the
pinned call support supplies the callee context, the cut, the pop and the
handler jump.

`loopWordPrice` is the price of each Word node:

| Word node | Price |
|---|---|
| `Skip`, `Seq`, `MustTerminate` | 0 (`MustTerminate`'s body is recursed) |
| `Tick` | 1 (lowered to a native `Skip`) |
| `Assign` | its expression work (the root node is the move) |
| `Set`, `Store`, `ShareInst` | 1 + expression work |
| `Return` | 1 + values |
| Tail call | its arguments, including the return location |
| Returning call | its arguments, plus its return names only when the callee body actually returns a value of that arity with the clock nonzero |
| Other leaves | 1 |

The returning-call price depends on the state. The native return suffix of
`WordToStack` runs only on the return path, so the call pays for it only
there.

The literal `RiscV/WordToStack` lowering ignores Word cutsets, so the price has
no cutset component.

### Price changes in `LoopWork` and Crep work

A compiled Loop `loop` is `Tick; loop; Tick`. To pay for it, a `LoopWork`
loop iteration now costs 3, and a `CrepWorkP` `while` iteration costs one more
unit. The coarse and sharp Pan-to-Crep `while` proofs absorb this with their
existing slack, so `sharpScore` is unchanged.

### Production route

The runtime image is built in `RiscV/SourceRuntimeBackendOutput.lean`, lines
40–60. It lowers `panToWordCompileProg loop` directly. `wordProgDCE` there
builds only `discoveryWords`, which are used for FFI-name discovery and are
never lowered. The executed Word code is therefore exactly the
`loop_to_word` output, and no DCE cost step is needed.
