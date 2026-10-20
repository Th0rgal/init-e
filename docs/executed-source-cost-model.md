# Executed Pancake work

The participant goal is a verified RISC-V ceiling at most 900,000,000,000 steps.
The challenge semantics/compiler pin remain unchanged. Pancake's semantic clock
is a termination index, not the execution-work metric. The final source bound,
whole-compiler transfer and finite certificate are still unfinished;
`Solution.claimedScore` remains infinity.

## Source accounting

Namespace `InitECandidate.Runtime.FineCost` uses typed `WorkEvent` traces.
`PanWorkVector.Work` records statements, expressions, scalar operations, memory
accesses, moved words, frame slots, transfer bytes, primitive blocks and native
events, global-access counts and global words. `executionWork` adds events; `Work.score` takes a dot product with a
coefficient vector. Both compose additively over trace concatenation.
Coefficients must be justified by compiler/runtime proofs; a source unit does
not automatically equal one native instruction.

Each executable statement and evaluated expression pays one entry event.
Structural `Seq` emits no event: its children concatenate their actual traces,
so preprocessing reassociation cannot change the cost. Crep and Loop sequencing
are also free; Loop `Skip` costs zero because it emits no operation. Children
are charged separately, only the chosen branch runs, and every loop guard
(including the final false guard) is charged. Calls include actual argument
work, body, selected handler/continuation and argument/result copies. Errors,
exceptions, rejections and timeouts retain their executed prefixes.

| Operation | Size accounting beyond entry/children |
| --- | --- |
| Fixed-width arithmetic/comparison/shift | Scalar operation count; numeric magnitude of a 64-bit constant is not a work count |
| Variadic operation | Operand/reduction work, with all evaluator children retained |
| Global reads/writes and call results stored into globals | Dedicated `globalAccess words` event records fixed setup separately from flattened words; local reads are unchanged |
| Structured variable/construction/projection/copy | Actual flattened words produced/moved |
| Structured memory | Logical scalar accesses for the requested flattened shape; rejection conservatively pays request size |
| Byte/32-bit memory | Logical access count; native coefficient must cover admitted alignment expansion |
| Function frame | Argument/result words, frame slots and saved/restored work where accounted |
| External/shared operation | Guest-side transfer/setup plus native events; no invented host-computation charge |
| Hashing/trie/hashmap/key comparison | Actual blocks/bytes/probes/visits/comparisons; no assumed constant-time lookup |

`PanTotalExpressionCost` defines total `expressionEvents` and list/field event
functions for every source expression, following exact evaluator guards.
`CostedExpressionRun` ties the exact result to these canonical events.
The older partial `PanExpressionWork` relation is not the canonical full model.

`PanStatementWork.StatementRun` covers all 21 source program constructors,
including malformed and failing outcomes. Recursive bodies have recursive
traces; atomic FFI/shared leaves retain exact leaf evaluator premises and event
accounting. `StatementRun.sound` erases to exact evaluation.
`PanCallCostPlan`, `PanExternalCost` and `PanCostCompleteness` support the complete
call/handler/external rules.

`PanCostTotal.source_evaluation_cost_trace` proves global trace existence for
every state/program evaluation. `sourceExecutionEvents` selects a certified
trace, and `sourceExecutionCost` scores it. `sourceExecutionCost_spec` connects
this definition to `StatementRun`. `PanCostDeterminism` proves event-list
uniqueness for ANY two source runs from the same state/program, including
failures, timeouts and overlapping invalid-value rules.
`sourceExecutionCost_eq_of_run` identifies the functional cost with the exact
price of any concrete actual trace, and `sourceExecutionCost_le_of_run` lifts
a witness price bound directly to that functional cost. No trace-choice
hypothesis or quantitative oracle is needed.

## Return-slot frame accounting

After successful callee lookup, call Done/Handler/Timeout traces also charge
`frame (sizeOfShapeWithContextHOL state.structs returnShape)`. Declaration-call
Return/RejectedReturn/Stopped/Timeout traces instead charge their declared
shape. This pays compiler return-slot initialization even before timeout or a
callee exception; forms that allocate no slots are conservatively charged too.
Argument/lookup failures remain unchanged. The source compiler transfer can
therefore pay by the actual requested size instead of a universal return-size
cap or an inflated coefficient on every statement. Completeness and erasure
remain exact; the checked source-to-Crep transfer uses this size event directly,
without a universal return-slot bound.

## Checked compiler pieces

| Stage/modules | Proven result | Scope/remaining obligation |
| --- | --- | --- |
| `SourceCostCrepWork`, `SourceCostCrepBasis`, `SourceCostCrepLeaf`, `SourceCostCrepDec`, `SourceCostCrepCall`, `SourceCostCrepHandler`, `SourceCostCrepDecCall`, `SourceCostCrepPrimitive`, `SourceCostCrepAtomic`, `SourceCostCrepControl` | Executed Crep work paid by source events for control paths, declarations, local assignments, stores, returns/raises, calls/declaration-calls, primitive/external/shared operations, including caught exceptions and timeout; return slots paid by requested size | All localized constructors under original state/code/exception/locals relations and non-error result, with program/callee bulk-load premises; structures/globals preprocessing and whole-program entry remain open |
| `AllocCostModel`, `AllocCostSSA`, `AllocCostPasses`, `AllocCostCompose`, `AllocCostExecuted` | SSA prologue/instruction moves, three-to-two rewrite-site costs, nonamplifying allocation/colouring, and actual path budget for their composed output | Certified straight-line fragments; recursive call/loop reconciliation remains open |
| `AllocCostOptimizer`, `AllocCostCse`, `AllocCostUnreach` | Local static envelopes for must-terminate/dead-code removal, copy propagation, CSE, sequence cleanup and unreachable removal; expansion charged by rewrite sites | Straight-line fragment bounds; grammar/composed optimizer and dynamic control transfer remain separate |
| `AllocCostReconcile`, `AllocCostSSAControl` | Static local syntax envelopes for renaming, reconciliation, loop setup/back-edges, break/continue targets and tail-call argument moves, using actual live sets | Dynamic semantic execution transfer must still charge each occurrence; returning-call composition remains open |
| `SourceCostCrepSimp` | Actual arithmetic simplification never increases executed Crep work, including calls and handlers; original result/state relation retained | Same clock; no recursive cost multiplier |
| `SourceCostLoopCode`, `SourceCostLoopLeaf`, `SourceCostLoopTransfer`, `SourceCostLoopIf`, `SourceCostLoopDec`, `SourceCostLoopWhile*`, `SourceCostLoopCall*`, `SourceCostLoopControl`, `SourceCostLoopSource` | Full localized source-to-Crep-to-arithmetic-simplification-to-Loop per-statement execution transfer, with real guards, actual iterations/callees/handlers and all original compiler relations; optimizer premise discharged | Generic factor-seven coverage envelope is too loose for final score; structures/globals preprocessing and whole-program entry still open |
| `SourceCostSharp*`, `SourceCostLoopPrice`, `SourceCostLoopPricing`, `PanSharpCost` | Source-to-Crep-to-simplification-to-Loop transfer at factor ONE, with opcode-sensitive local expression prices and per-site certified address replay; canonical selected source cost equals any concrete trace price | Every localized constructor under original semantic relations, non-error result, `sharpSitesProg 40` for program/callees; structures/globals and installed entry remain open |
| `SourceCostPanSimp*` | Full pinned `pan_simp` sequence reassociation, tail-call rewriting and installed-callee code-map transport preserve/decrease source event costs under EVERY coefficient vector | Actual source traces retained, including timeout/exception prefixes; structures/globals passes separate |
| `SourceCostLoopWork` | Output-indexed exact Loop execution work, soundness and equal-work lifting to a larger clock for non-timeout runs; selected branches, each loop iteration, callees/continuations/handlers exposed | Actual Crep-to-Loop transfer is a separate stage |
| `SourceCostLoopOptimise` and `SourceCostLoopLive*` | Full actual call rewrite, liveness shrink and marking preserve or decrease executed work at coefficient ONE, under original terminal-result guards and exact original initial/final states | Discharges `LoopOptimiseWork`; no recursive optimizer multiplier |
| `AllocCostSSAExecuted` | Actual-state executed budgets for reconciliation and setup fragments, back-edge work at each reached intermediate state, and break/continue exit moves | Whole-loop SSA semantic iteration induction and returning-call exception composition remain open |
| `CrepExpressionWork`, `PanLoweringAllowance` | Full local source expression expansion; context-width and repeated address work retained | Generated syntax, not complete statement execution transfer |
| `CrepToLoopLocalBound` | Generated code plus residual expression work <=6 times Crep expression work; list materialization potential | Local expression lowering |
| `LoopExecutedWork` | Sound, complete, bounded actual traces for generated expression-code subset | Calls/loops rejected by the static subset cost |
| `PanLayoutCost`, `PanReadPresence` | Successful reads and original compiler locals relation discharge width/presence conditions | Actual successful source expression premises retained |
| `PanBulkExpressionCost`, `GuestBulkLoadSites`, `GuestBulkLoadApplicability` | Every pinned guest load site has <=6 words and scalar well-formed address; compound source allowance composes with one factor six; local source-to-Loop factor36 | Source preprocessing and full statement execution remain separate |
| `LoopToWordExpressionWork`, `LoopToWordCodeWork`, `LoopToWordValueCost` | Exact work preservation and pinned value simulation | Loop topAddr costs5; comparison materialization costs2 including tick |
| `WordPullWork`, `WordFlattenWork`, `WordSelectionWork` | Pulling nonamplifies; binary flattening factor-two potential; full assignment selectedLeaves+1 <=2*expressionWork | Syntactic local selection bound |
| `WordSelectionStraightLine`, `WordSelectedPathCost` | Actual selected Word path <=4*expressionWork, including early exits | Certified selector grammar |
| `WordSelectedStackCost` | Original Word-to-Stack simulation with that additional-clock budget | Retains original compiler/resource premises; not final native steps |
| `WordNativeInstructionCost`, `WordNativeMoveCost` | Integer instruction <=4 Stack leaves including reloads/spill; singleton move <=2 leaves | Any frame assignment; no whole-frame multiplier |
| `ParallelMoveCost`, `WordNativeParallelMoveCost`, `AllocatedNativeCost` | Literal scheduler emits <=2 copies per input move including cycle saves; native parallel move <=4*moveWords+1 leaves; allocated straight-line output <=4*nodeCost leaves and actual pre-removal path <=16 times the composed local SSA/rewrite budget | Includes arbitrary moves/spills; remaining optimizer passes and recursive control separate |
| `NativeFrameSlots` | Every native instruction reload/spill and scheduled move stays within its actual frame; direct frames have removal units equal to Stack leaves; allocated straight-line post-removal path <=16*Word node envelope | Requires the frame<=92 fact, discharged from actual frame-table membership; no frame-size multiplier |
| `NativeControlSlots` | Native frame-slot bounds recurse through conditionals, loops and must-terminate wrappers, including register reloads and invalid-immediate materialization; actual function prologue preserves the computed frame bound; every nested offset is directly encodable for frames<=92 | Control skeleton with certified allocated leaves; call/return frame transitions remain separate; this is access eligibility, not a runtime-step bound |
| `GuestFrameCost` | Kernel certificate of actual frame-table maximum92 and target direct-address checks for slots0..92; a load/store within such a frame has removal cost1 | Applies when actual frame membership and slot<=frame are proved; no 92-fold cost multiplier |
| `WordSelectionNativeCost` | Complete selector grammar has <=4 Stack leaves per selected Word leaf; actual pre-removal path <=32*Word/Loop expression work; original flatten simulation | Optimizer/SSA/allocation and Stack removal are separate |
| `StackAddressCost`, `StackRemovalLocalCost` | Literal address shifts use slots/255+1 chunks; directly encodable spill offsets cost1, fallback load <=chunks+2, fallback store <=2*chunks+1; actual removal output path <=4*sum of local units | Costs each actual slot offset; original flatten simulation retained |
| `WordPathWorkCorrect`, `StackPathWorkCorrect`, `StackRemovePathWorkCorrect` | Complete semantic/compiler simulations with actual successor-state budgets | Quantitative caps must be supplied by executed-work proofs |

Structured source loads compute the address once, but `loadShapeBytesHOLW` may
replay the compiled address per output word. Its bound is
`words * (addressWork + 3)`. The guest certificate's scalar-address restriction
lets the compound bound compose once, without multiplying six at every nested
load. `scalarLoweringWeights` (expressions4, movedWords1) is a local proof
weighting, not a final universal native coefficient table. Named structures and
globals still need their earlier preprocessing linked to the work transfer.

## Label-to-native execution

`LabWeightedInstructionTrace` charges visited native expansions, never the size
of unvisited ROM. `LabWeightedMixedTrace` composes ordinary instructions with
returning FFI/shared-memory operations while preserving the interference oracle.
`LabWeightedExtract` derives these traces from actual successful supported label
evaluation and proves native steps <=weighted work+17, including terminal FFI,
shared and normal halt outcomes. No runtime trace or native run is assumed.

`LabWeightedInitialization` derives initial relations from the original guards.
`CompiledWeightedNative` composes actual compilation/installation, retaining the
`removeLabels` equation that identifies the cost-bearing compiled code.

`AsmLocalCost` uses checked opcode bounds: common binop/memory/div/skip cost1,
constants their actual expansion length (<=6), shifts <=5, jumps/calls/location
materialization2, branches3 and remaining complex instructions16.
`NopLocalBudget` proves one step per padding NOP. `LabInstructionLocalCost`
charges a fetched ordinary instruction by opcode cost plus only padding bytes
beyond its actual encoding, divided by four. The weighted instruction trace uses
this sharper ordinary-instruction charge. `LabControlLocalCost` also bounds indirect jumps by1, direct jumps by2 and
taken branches by3. Fallthrough branches and location values use their local
base cost plus the visited line-word allowance; no ROM-size factor remains
in the weighted trace.

## Checked guest amortization

`GuestCostGasBudget` proves the executed-work budget for an exact loop trace
under an explicit reachable invariant `I`. Each continuing body run must
preserve `I` and increase the funding measure by at least one; every body run
costs at most `C * consumed + B`, and a statement/guard evaluation costs at most
`D`. The loop bound is `(C+B+D) * consumed + (B+D)`, including terminal,
rejecting, malformed-guard and timeout prefixes. No gas progress is required on
terminal paths. `GuestCostFundingMeasure` identifies the actual frame's used-gas
cell at offset184 and obtains positive progress from installed `charge_gas`
evaluation under funding/layout premises. These are checked reusable contracts;
the actual interpreter body cost and reachable invariant remain to be proved.

The checked `GuestCostWorkScore`, `GuestCostCallRule`, `GuestCostSequence` and
`GuestCostAtomicExpressions` provide additive event prices and local trace
composition. `GuestCostChargeFamily` traces and prices the pinned `charge_gas`
successful body and out-of-gas prefix; `GuestCostArithmeticFamily` pins and
traces both `add_sat` helper paths. Combined imports with the compiler transfer
are checked in `GuestCostCombinedSmoke`. These do not cover any complete EVM
opcode arm yet. The installed `charge_gas` call theorem now supplies its concrete trace and
price together. `GuestCostPcAdd` pins the actual `pc_add` body and derives its
stored value from the frame cell/domain and local `n`, then traces and prices
the body. Universal trace/body bounds remain separate from these explicitly
constructed helper traces.

`StackWeightedInstruction` now derives an exact weighted label trace from the
original Stack instruction flattening hypotheses, then composes it with the
RISC-V local simulation. The result includes the actual native prefix, its
opcode-plus-padding bound, the related successor and the advanced oracle tie.
`LabWeightedComposition` adds weighted instruction and mixed traces with no
extra factor or terminal surcharge per block. `LabWeightedClock` lifts a finite
successful instruction prefix to any larger label clock with identical work.
`StackWeightedBlock` derives an exact weighted trace for an actual compiled
ordinary-instruction sequence under the original flattening hypotheses. It
proves source trace existence from successful Stack evaluation, erases only
zero-step labels from the installed pattern, and obtains an actual RISC-V
prefix bounded by the sum of each visited opcode/padding cost. Related states,
program counters, code and the oracle tie are retained.

`StackWeightedControl` supplies real flattened Break and LocValue prefixes under
the original `FlattenHyps`: direct jump allowance 2, local materialization/padding
for LocValue. Returning to an explicitly valid installed location uses one
native indirect jump. `StackWeightedBranch` proves the actual compiled layout
of two nonempty ordinary instruction arms. `StackWeightedIf` covers both actual
conditions and composes the selected arm with its branch and, only when reached,
its join jump. `flatten_instructionBlock_if_native` yields the RISC-V prefix and
retains the original related successor, PC, code and oracle. General branches
with returning arms, loops/calls, and the bridge from generated expression
fragments to these instruction blocks still need composition.


`SourceCostLoopOptimise.loop_optimise_executed_work` proves the full pinned
optimizer nonamplifying at coefficient ONE. `LoopWork.live_paid` covers every
non-error shrink constructor, including actual loops, return continuations,
exception handlers and early-call timeouts. The original semantic correctness
theorem identifies successors of independently constructed costed traces; it
supplies no quantitative oracle. Saved-local projection lemmas extend ownership
by actual returned values or exception bindings. Known-label call rewriting
retains callee/environment and removes only the target argument charge.
Marking preserves exact work. The original terminal guards and original initial
and final states are retained by the combined theorem.

The sequencing refinement was independently checked through global source trace
completeness and all existing localized source-to-Crep modules. The complete
source-to-simplified-Crep-to-Loop per-statement transfer and five-module pan_simp
execution/code-map transfer were source-reviewed and independently replayed from
worker snapshot966c5a8d2. The former preserves all original compiler relations and
uses the proved optimizer interface. The latter is nonamplifying under every
coefficient vector, including reached compiled callees, continuations and
handlers. Structures/globals preprocessing and whole-program entry remain open.
The existing guest sequencing, charge_gas, add_sat and pc_add helper modules
were migrated to exact Seq-free event lists and independently replayed with
gas amortization, funding, call-rule, atomic-expression and combined-import
checks. New StackPop/U256Add/StackPush/op_add helper snapshots are still queued
for independent review/replay; no complete opcode/interpreter bound is claimed.

## Numerical budget audit

The generic `sourceCrepWeights` followed by the factor-seven Loop bound remains
a coverage envelope. It prices the stated Seq-free `u256_add` vector at 13,832
Loop units, already exceeding gas-3 ADD's 13,500 native-step allowance at the
overall 900-billion/200-million ratio before other helpers.

The integrated sharp route instead prices the SAME canonical events as
`10*statements + 5*expressions + 5*movedWords + 12*memoryAccesses + 4*frameSlots
+ 40*globalAccesses + 17*globalWords + 45*replayUnits`. Replay units sum `k-1`
for each `.memory k` or `.globalAccess k` event. A static
`sharpSitesProg 40` certificate bounds the compiled address-head price at multiword
load sites; no whole-program expression maximum is multiplied into all work.
The source-to-Loop theorem preserves this allowance with factor ONE through
arithmetic simplification and the installed Loop optimizer. The stated
`u256_add` counts yield 836 Loop units (checked numeric lemma). This is not a
native score: whole ADD/interpreter bounds, downstream compiler prices,
initialization and nongas input processing remain to be composed.

`PanSharpCost.sourceSharpExecutionCost` scores the unique actual source event
trace at these prices. `sourceSharpExecutionCost_eq_of_run` connects any concrete
guest trace to that function; `sourceSharpExecutionCost_pays_loop` applies the
compiler theorem directly to it. Worker snapshot bb442a0d3 was frozen, its price
and semantic interfaces reviewed, and all 56 source compiler-chain modules were
independently rebuilt. The selected-cost bridge was checked separately.

The global-access accounting from worker snapshot `01c6a5439` was independently
rebuilt through 52 source/compiler modules, including completeness and unique
canonical traces. A global access records both an occurrence and its flattened
word count so even zero-word accesses can pay fixed setup. The sharp global
allowance is `40 + 17*n + 45*(n-1)`; local expression and ordinary memory prices
are unchanged. The actual statement-level `pan_globals` transfer is now checked below;
installed-entry initialization remains a separate obligation.

`pan_simp` now preserves every additive per-event price, including replay and
global-access charges. `SourceCostPanStructsId` proves structures preprocessing
is the identity under a checked syntactic no-named-structures predicate;
`SourceCostCrepInlineId` proves Crep inlining is the identity when no function
is inlinable. `GuestCostSyntax` checks both predicates on the actual simplified guest. The
post-globals no-inline predicate remains to be checked.

`SourceCostSharpHead` bounds the exact compiled head expression that structured
loads reevaluate per additional word. A record field of a local selects one
compiled variable or constant, regardless of the entire record size. The
supported address grammar includes these fields and nested loads. The former
whole-address replay estimate and its narrower grammar have been removed.
`GuestCostSharpSites` certifies `sharpSitesProg 40` on the exact pass0 and pass2
declarations, including the generated entry. This repairs the previously
failing guest certificate. Root independently rebuilt all 38 affected modules
in `sharp-head-independent`, including both concrete certificates, with only
standard Lean axioms. Neither the fixed replay coefficient nor the guest source
was changed.

Existing root guest helpers were replayed with the new model. Generic
`callEvents`/`callLocalCost` accept optional final call info (default `none`)
and include the global-write event/price when applicable; the generic installed
`charge_gas` call theorem retains arbitrary destination info. `expressionCost_var`
retains the extra global price explicitly. New worker opcode/invariant modules
remain queued for review and migration after their current live check.

## Actual Word execution counter

`WordExecutionCost` defines price-parametric work on the actual Word execution
path, including reached call bodies, handlers, continuations and MustTerminate
bodies. `wordLogicalPrice` gives structural Seq/Skip zero price and explicitly
charges expression sizes, parallel-move words, return words and argument words.
It is a logical instance, not an asserted native instruction coefficient table.
The older `wordPathWork` remains a separate additional-Stack-clock allowance.

`WordExecutionCostProps` proves exact sequencing, monotonicity, zero-price work
and move sizing. `LoopToWordExecutedCost.loop_to_word_executed_local` turns the
existing supported local-code certificate into an actual execution bound for
every Word entry state. Its supported subset excludes calls and loops; those
transfers and native pricing remain obligations. All three modules checked with
only the standard proof axioms. `WordExecutionCostAlgebra` proves exact additive and scaling laws, and a
pointwise two-component price envelope transfers to the same linear execution
envelope. These laws do not insert a multiplier at calls or loop nesting.

## Composing native prefixes

`StackWeightedCompose.NormalWeightedFlatten` is the recursive compiler motive
for normally returning, code-preserving fragments. Ordinary instruction blocks
discharge it using the original flattening hypotheses. The Seq rule joins
actual weighted subtraces at the reached source and label states, preserving
ABI metadata and adding no structural native cost. Its native theorem executes
the composed prefix on RISC-V and preserves the oracle tie for continuation.
`StackWeightedComposeIf` grounds the motive for actual selected conditionals
with nonempty ordinary arms. Layout positions include both arms; runtime work
includes only the selected arm and its actual control instructions.

These checked rules cover normal prefixes. They do not assert a complete
compiler theorem for calls, loops, terminal results, code installation or
resource exits; those need their corresponding recursive rules and concrete
Word-to-Stack price justifications before an end-to-end score can be derived.

`StackWeightedExit` adds a separate recursive motive for nonhalting control
exits. It retains the actual installed destination and distinguishes a reached
location from Continue's pending back jump. Checked leaves cover Break (native
allowance 2), Continue (prefix allowance 0), and Return/Raise to semantically valid
installed locations (allowance 1). Early-exit Seq discards its untouched suffix;
normal-prefix-to-exit Seq joins only the reached traces. The composed exit has
an actual RISC-V prefix theorem with related state and advanced oracle tie.
`StackWeightedLoop.normalWeightedFlatten_loop_break` covers the final iteration
whose body returns Break 0: the break's existing jump reaches the loop exit and
Loop/labels add no native charge. `StackWeightedLoopLayout` shares the actual
body installation, entry/exit locations, back-jump fetch and label-length facts
across cases. `normalWeightedFlatten_loop_step` and `_loop_continue` compose
actual normal/Continue 0 iterations with the recursively certified next run,
at price `bodyPrice + 2 + restPrice`. The back jump consumes the original
semantic-clock tick while its native work is charged separately; no recursion
or nesting multiplier is introduced. `exitWeightedFlatten_loop_exit` transfers
noncontinuing control exits using the original index-pop rule and unchanged
return/exception locations. `StackWeightedLoopExit` composes normal/Continue 0
iterations when a later iteration has such an exit, at the same additive
`bodyPrice + 2 + restPrice` ceiling. Terminal/resource outcomes and a complete
recursive driver still need their remaining rules.

`StackWeightedTerminal` connects an actual flattened Halt operand to its exact
success/resource-limit outcome and final FFI state. Its recursive motive carries
the actual weighted prefix plus a literal terminal witness. Normal-prefix and
early-terminal Seq rules compose without terminal surcharges per child;
`StackWeightedLoopTerminal` handles terminal bodies and normal/Continue 0
reentry into a later terminal iteration. Native extraction charges at most
`prefixPrice + 17`, with the terminal ceiling appearing once. These are checked
compiler constructor rules; the complete recursive compiler driver and the
remaining FFI/shared/call leaf constructions still need completion.

`SourceCostGlobalsExpr*` proves successful ready expressions preserve their
values and do not increase the sharp source score under the original globals
state relation. `SourceCostGlobalsState` supplies actual clock/locals/callee
relations; `StatementRun.code_eq` reuses the pinned evaluator's code-preservation
theorem. `SourceCostGlobalsReady` exposes the syntactic requirements for the
remaining statement transfer. `GuestCostGlobalsReady` checks these on the exact
pass1 declarations: every body and initializer is ready, function parameters
exclude the generated call temporary, and body readiness follows from actual
declaration membership. The statement-level globals transfer is now checked as described below;
installed-program entry still requires its separate composition.

`StackWeightedSkipIf` proves the literal layout for a nonempty then arm with
an empty else arm. A true source guard executes the negated branch's actual
fall-through and the selected arm, for normal, control-exit or terminal results.
A false source guard jumps over the body for allowance 3; the skipped body
contributes no work. The shared layout includes its actual emitted label counter
and installed end location. Other conditional layouts remain to be generalized.

`AllocCostSSAPermStack.wordPathWork_permStack_variant` proves equality of
`wordPathWork` across stack permutations for every Word constructor under the
original `permStack` relation and no-allocation/no-installation program and code
restrictions. Its recursive proof has no recursive cost assumptions. The
supporting call transport covers successful, exceptional and failing prefixes.
`AllocCostSSABodyWork` expands compiled calls into inserted moves, callee body
and reached return handler; its remaining cost premises concern those bodies,
not the whole call. `AllocCostSSALoopExecuted` charges reconciliation on every
actual iteration, but instantiating its one-body simulation for the complete
SSA pass remains open. All 15 allocation dependency modules independently
checked in `perm-stack-independent` with only standard Lean axioms.

These statements concern the existing additional-clock counter `wordPathWork`.
They do not yet prove transfer of the finer, price-parametric
`WordExecutionCost`, nor do they supply the final native instruction budget.

`StackWeightedThenSkipIf` reuses the empty-else weighted proofs for an empty
then arm through equality of the literal compiler output and successful source
evaluation under a negated guard. Normal, control-exit and terminal outcomes
retain the selected body's price. Selecting the empty arm costs only the taken
branch (3); when both arms are empty the compiler emits no branch and the native
prefix costs zero. The complete module checked with standard axioms in
`stack-then-skip-if4`.

`AllocCostSSACallAlignment` derives actual inserted stack/argument move runs,
renamed reads and paired cuts from the original SSA state invariant and pinned
returning-call preparation lemmas. It also derives swapped-stack pop alignment
from the original callee stack relations. The assembled local bound retains
callee lookup/result protocol and body/continuation cost premises; eliminating
these through the checked permutation theorem and recursive SSA induction is
still required. The root replay `call-alignment-independent` checked all seven
printed theorems with only standard axioms.

`SourceCostGlobalsRun.globals_compile_run` transfers every non-error canonical
statement run through actual `pan_globals`, preserving the original compiler
state relation and never increasing `sharpSourceScore B`. The replay coefficient
remains parametric. Its premises include ready syntax/code, absence of the
reserved temporary, and presence of every laid-out global. Global presence and
temporary exclusion are preserved through the actual source runs. A global
call destination is charged at entry using its declared value size, including
timeout paths, to pay for the compiler temporary before the callee returns.
`SourceCostGlobalsCanonical` derives the same factor-one inequality for the
functional selected execution cost, without an additional trace witness or cost
oracle. Independent root replays checked all 63 affected modules and both
canonical corollaries with standard axioms. Installed-entry initialization and
the downstream native composition remain open.

`StackFlattenShape` proves the exact emitted instruction length and
nonreturning flag for every Stack constructor, including calls and all six
conditional layouts, independent of section/label numbers and loop labels.
This supplies static PC offsets for compositional native proofs without adding
unselected code to runtime costs. Its recursion and three geometry corollaries
checked in `stack-flatten-shape8` with only standard axioms.

`StackWeightedGeneralIf` lifts arbitrary selected bodies through the actual
two-nonempty-arm join layout when both static nonreturning flags are false.
Normal, control-exit and terminal outcomes are handled on both guard values.
Only normal completion of the first emitted body pays the join jump (2); exits
and terminal prefixes omit it. The unexecuted body contributes only its PC
offset. The layout and six composition theorems checked independently in
`stack-general-if-full2`. The two layouts placing a statically nonreturning
body first remain to be composed.

The recursive `NormalWeightedFlatten`, `ExitWeightedFlatten` and
`TerminalWeightedFlatten` motives now carry `WeightedMixedTrace`, so reached
FFI/shared returns can compose with ordinary execution. `LabWeightedMixedClock`
embeds ordinary traces without changing their price, lifts all three kinds of
work across additional label-clock supply, and proves installed code and ABI
register indices survive returned operations. Native extraction retains the
actual advanced machine configuration (including FFI interference), target,
encoder and oracle tie. The final terminal allowance remains 17 once after
the full prefix. Independent replays `lab-mixed-clock2`, `mixed-stack-controls`
and `mixed-stack-controls2` checked the support lemmas and all twelve affected
native composition/geometry modules. Actual Stack FFI/shared leaf construction,
remaining conditional layouts and the complete recursive driver remain open.

`StackWeightedFfi` constructs the actual compiler-produced external-call trace
from `FlattenHyps`. Successful source evaluation supplies operand reads, byte
reads and the returned FFI response; the original ABI relation protects the
argument registers during return-label materialization. A returning call costs
`controlWork 2 encoded pc + 17` and preserves the exact returned memory/FFI state.
A final call charges only materialization in its prefix and leaves the final
allowance to `TerminalWeightedFlatten.native` once. Both cases independently
checked in `stack-weighted-ffi4`; no native-run or cost premise is assumed.

`StackWeightedShared.sharedStep_of_source` derives exact LabSem dispatch and
successor state for all eight shared-memory load/store operators from the
actual Stack run and original compiler relation. It preserves domain/alignment
checks, access-size encoding, returned values/FFI state and the clock-zero case.
`normalWeightedFlatten_shared` constructs the returned mixed trace with cost1;
`terminalWeightedFlatten_shared` supplies a final dispatch with an empty prefix,
leaving the terminal allowance to the existing extraction theorem. All three
statements checked with standard axioms in `stack-weighted-shared3`.

`StackWeightedNoRetIf` completes the two conditional layouts that place a
statically nonreturning arm first and emit no join jump. It derives actual code
positions and selected mixed traces for exits/terminal outcomes on the first
arm and all three outcomes on the second. The two layout theorems and ten
composition theorems checked in `stack-no-ret-if` with only standard axioms.
Together with the empty-arm and general-layout modules, all six compiler
conditional layouts now have checked local composition rules. A complete
recursive compiler driver still needs to instantiate these rules.

`SourceCostFperm` preserves the exact source events when globals lowering
renames the original entry. `SourceCostSimpTop` transfers installed declaration
code through pan_simp, and `SourceCostSourceTop` composes that with structures
identity and actual globals initialization. `SourceCostLoopTop.source_loop_top`
then carries the ORIGINAL entry-run cost to the actual installed Loop entry,
retaining the original run relation and non-error outcome. Its remaining
`EntryPipeline` premises are the pinned compiler state relations, code maps,
entry lookup and static certificates, rather than quantitative transfer oracles.
They still need discharge for the concrete challenge initial states.
The one-time source allowance is `20 + 4*returnShapeWords + 57*globalCount +
5*payloadWords`. `GuestCostGlobalsInit` checks the actual pass1 has 93 constant
global initializers, so the store subtotal is 5301. Independent root replays
`source-entry-independent` (8 modules) and `source-loop-top-independent`
(strengthened non-error result and six affected modules) passed with standard
axioms. This is not the final native budget or a complete guest gas bound.

`SourceCostInitial.source_loop_initial` discharges `EntryPipeline` at the
pinned compiler initial states: it constructs the globals state, installed Crep
state and installed Loop state, deriving their code/domain/exception relations
from the original compiler initialization premises. The cost remains the
original source trace plus the one-time initialization allowance. Root replay
`source-initial-independent` checked this and its pipeline facts module with
standard axioms. Instantiating the remaining Word-target initialization premises
and all guest certificates for the concrete input is still required.

`StackWeightedLeaves` grounds the recursive native motives for Skip, literal
instructions, location materialization and Tick. The prices retain each visited
opcode/padding cost. Tick uses its original source clock tick, with no added
label clock. All four leaf theorems checked in `stack-weighted-leaves2`.

## Remaining end-to-end obligations

1. Execute-cost transfer through structures/globals preprocessing and actual
   installed-program entry. Localized source-to-simplified-Crep-to-Loop and
   pan_simp transfers are checked; retain their original semantic premises and
   explicit load-site certificates while sharpening numeric costs.
2. Word optimizer/SSA/allocation cost transfer, charging inserted moves at each
   actual execution site, including loop/call reconciliation.
3. Compose downstream local work across full control flow and native encoding;
   retain initialization, terminal overhead and resource-limit behavior.
4. Bound actual guest `StatementRun` work from input size, consumed gas, memory
   and algorithm invariants. Gas progress is needed for continuing iterations;
   terminal/rejecting prefixes need their own overhead allowance.
5. Compute the compiler-weighted numerical score, reserving nongas decoding and
   initialization costs, then run the authoritative verifier. A conditional
   finite certificate or a source score below900B alone does not meet the goal.

See `cost-theorem-audit.md` for retained/removed theorem families. Obsolete
whole-program affine certificate wrappers have been deleted; useful semantic,
geometry, ownership and progress lemmas remain available.

### Actual call entry and terminal tail calls

`StackWeightedCall.compileJumpEnter_weighted` enters the actual installed callee
with the original state relation and consumes the original source call clock
unit. It supplies an actual mixed trace costing two native instructions for a
direct target or one for an indirect target. `StackWeightedCallTerminal` composes
that jump with a reached terminal callee, adding its recursive budget once.
`StackWeightedCallEntry.callEnter_weighted` handles returning-call entry: it adds
only the visited return-location materialization price and the actual target
jump. The materialization needs one extra label clock unit; the jump uses the
source call unit. These results checked with standard axioms in
`stack-weighted-call4` (entry), `stack-weighted-call5` (terminal tail call), and
`stack-weighted-call-entry2` (returning entry). Returning continuations/handlers,
raw calls, and the complete recursive native driver remain open.

The original/generated entry correspondence now preserves the exact result,
not only non-error status. Concrete guest main signature, struct context, and
pass2 no-inline/localisation certificates checked in
`source-outcome-independent` and `guest-entry-syntax3`. This does not yet provide
the whole guest gas bound or a finite submission score.

`StackWeightedCallReturn.terminalWeightedFlatten_call_return` now composes an
actual callee returning to its installed location with the reached terminal
continuation. The price adds the call materialization, direct/indirect jump,
callee work, and continuation work at `pc + 2`. It permits an arbitrary
installed exception handler: that handler and the post-continuation join are
not executed on this terminal path. The proof reconstructs installation, ABI,
clock, and exact return-PC facts from the original relations and actual callee
evaluation; it assumes only the recursive child cost motives. Checked with
standard axioms in `stack-weighted-call-return7`. Normal/other exiting
continuations and executed exception-handler paths remain open.

### Returning continuations and executed exception handlers

`StackWeightedCallReturnPrefix` factors the actual reached-return prefix,
including the original evaluation, exact return PC, compiler state/ABI relation,
installed continuation, and mixed trace. `StackWeightedCallReturn` now reuses
this prefix. `StackWeightedCallReturnControl` adds control-exiting continuations
with arbitrary installed handlers and normal continuations without a handler.
`StackWeightedCallReturnJoin` adds the normal-continuation case with an installed
handler, charging exactly the reached two-instruction join jump and no handler
work. These checked in `stack-call-return-prefix1`,
`stack-call-return-compose1`, and `stack-call-return-join1`.

`StackWeightedCallHandlerPrefix` constructs the actual raised-callee path to
the installed exception handler. `StackWeightedCallHandler` then composes all
three handler outcomes: normal, control-exiting, and terminal. The return
continuation is unexecuted; its static instruction count locates the handler
PC and is never added as executed work. These checked in
`stack-call-handler-compose4`. All printed axioms are standard.

These are local recursive constructor rules, not the completed compiler
bound. Callee terminal propagation, unhandled exceptions, other call forms,
and the full recursive driver and Word pricing transfer still need completion.
The full guest gas/input bound and finite submission score remain open.

### Propagated calls, raw calls, and JumpLower

`StackWeightedCallPropagate` charges actual returning-call entry and terminal
callee work when neither local continuation runs. `callResultPropagates`
excludes returns, Break, and Continue, and permits an exception only without a
handler. `StackWeightedCallPropagateExit` supplies the corresponding control
exit, including an unhandled exception. `StackWeightedCallExit` supplies tail
call exits.

`StackWeightedRawCall` and `StackWeightedRawCallExit` enter the actual installed
body at label 1, skipping the prologue. They charge the reached direct jump
(two native instructions) and body work. The original source clock unit pays
for the jump; no extra label-clock supply is inserted.

`StackWeightedJumpLowerFallthrough` prices the actual non-taken branch encoding
and leaves the source clock unchanged. `StackWeightedJumpLower` and
`StackWeightedJumpLowerExit` price a taken branch at three native instructions
plus the reached callee's terminal/control-exit work. Actual register reads,
comparison, lookup, installation, and original compiler relations justify the
trace. No callee or unused prologue is charged on fall-through.

Checks: `stack-call-propagate2`, `stack-raw-call1`, `stack-call-exits1`,
`stack-jump-lower2`, `stack-jump-lower-fall1`, and `stack-jump-lower-exit1`; all
printed axioms are standard. Full recursive compiler assembly and the transfer
from fine Word prices remain open; these constructor rules do not yet prove
a finite submission score.

### Price-parametric executed Stack cost

`StackExecutionCost.stackExecutionCost` follows the actual Stack execution
tree: a sequence charges only its reached suffix; a conditional its selected
arm; a loop its executed iterations; calls their reached callees and valid
return/exception continuations. RawCall skips the prologue. A tail call with
an invalid installed handler does not invent a callee execution. The local
price can depend on the operation and source state, permitting variable-size
operations to be charged by their actual size and structural nodes to be free.

`StackExecutionCostProps` proves the exact sequence equation, pointwise
monotonicity, zero-price identity, and additive decomposition for the same
execution. `StackExecutionCostAlgebra` proves scaling and a two-component
linear envelope. Neither loops nor calls multiply the coefficients. The
definition checked in `stack-execution-cost1`; all six laws checked with
standard axioms in `stack-execution-props8`.

This is the independent executed Stack cost model for recursive compiler
assembly. It does not assert that an arbitrary local price is a native cost.
Local opcode/padding/control bounds must be established from the actual
encoding, assembled through the checked weighted constructor rules, and
connected to the fine Word/source cost. The complete native theorem and
finite score are still unfinished.

### Connecting executed Stack cost to native traces

`StackExecutionNativeBasis.executionCostPrice` places the independent executed
Stack cost in the weighted native compiler motive. The module proves price
widening for all three outcomes and connects Skip, actual instruction
opcode/padding prices, and Halt to that model. Its instruction premise is a
local encoding-price inequality, not an assumed native run bound.

`StackExecutionNativeSeq` connects the actual sequence cost to native traces
for normal, control-exiting, and terminal reached suffixes, and for both early
exit forms. Unexecuted suffixes add no recursive cost.
`StackExecutionNativeLoop` connects all nine loop rules: normal/Continue0
reentry to each later outcome, final Break0, and propagated control/terminal
exits. A reached reentry needs a two-instruction local allowance; a stopped
iteration does not. The exact original source clock and relations are retained.

All results checked with standard axioms in `stack-execution-native-basis1`,
`stack-execution-native-seq2`, and `stack-execution-native-loop2`. Full
recursive compiler assembly, conditional/call integration with this model,
encoding-price instantiation, fine Word transfer, and the whole-guest bound
remain open. These results do not yet establish a finite score.
