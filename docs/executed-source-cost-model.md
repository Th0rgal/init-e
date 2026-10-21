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
| `SourceCostCrepWork`, `SourceCostCrepBasis` (the coarse per-constructor transfer modules were removed 2026-10-21; the sharp chain `SourceCostSharpCrep*` supersedes them) | Executed Crep work paid by source events for control paths, declarations, local assignments, stores, returns/raises, calls/declaration-calls, primitive/external/shared operations, including caught exceptions and timeout; return slots paid by requested size | All localized constructors under original state/code/exception/locals relations and non-error result, with program/callee bulk-load premises; structures/globals preprocessing and whole-program entry remain open |
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
traces both `add_sat` helper paths. These do not cover any complete EVM
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

### Complete conditional executed-cost interface

`StackExecutionNativeIf` derives the static normal-body flag from the actual
fall-through run, using the pinned `noRetCorrect` theorem. It connects the
executed cost to both selected normal arms across every conditional layout.
`StackExecutionNativeIfExit` covers both arms with control-exiting and terminal
outcomes. `StackExecutionNativeConditional` exposes one rule per outcome,
without requiring callers to choose a static layout. The selected body alone
contributes recursive work. The local price premise covers the actual branch
encoding plus at most the two-instruction join allowance; this is a local
price envelope, not a whole-program cost multiplier.

`StackExecutionNativeCalls` connects terminal/control-exit tail calls and raw
calls to the independent executed cost. The only local quantitative premise
is the actual entry-jump allowance; the callee's executed cost supplies the
recursive budget. Raw calls enter after the prologue.

Checks: `stack-execution-native-if3`, `stack-execution-native-ifexit2`,
`stack-execution-native-cond1`, and `stack-execution-native-calls1`; all printed
axioms are standard. Returning-call/model integration, recursive assembly,
concrete encoding-price bounds, fine Word transfer, and whole-guest gas/input
bounds remain open. The submission still claims infinity.

### Returning calls and remaining executed-cost leaves

`StackExecutionNativeReturn.executionCostPrice_call` gives the exact executed
returning-call cost after the actual callee run. Its six native rules cover
normal, control-exiting, and terminal return/exception continuations, including
the normal return continuation's join jump when a handler is installed.
`StackExecutionNativePropagate` handles terminal/control outcomes that execute
neither continuation. The propagation rules do not require a join allowance.

`StackExecutionNativeLeaves` connects LocValue, Tick, Break, Continue, normal
and final FFI/shared memory, and Return/Raise to the executed model. Return
and Raise retain their original installed-location validity premise; no
unchecked control destination is introduced. `StackExecutionNativeJump`
connects taken JumpLower terminal/control paths and its normal fall-through.

Checks: `stack-execution-native-return3` (including propagation),
`stack-execution-native-leaves2`, and `stack-execution-native-jump2`; all
printed axioms are standard. These connect constructor proofs to the cost
model. The complete recursive theorem, compiled-program eligibility and
return-location invariants, actual price-table instantiation, fine Word
transfer, and whole-guest gas/input bound still need completion. No finite
score is claimed.

### Recursive semantic-derivation to native theorem

`StackExecutionNativeKernel` unifies normal, control-exiting, and terminal
compiler conclusions. `LocalNativeCaps` lists explicit local opcode, padding,
control, and call-price inequalities. Its fields contain no native execution
or whole-run budget assumptions. `ExecutionLeaf.bound` proves the leaf cases.

`StackExecutionTrace` records finite semantic derivations over supported
post-removal leaves and every Seq/If/Loop/Call/RawCall/JumpLower flow. Each node
is tied to its actual evaluator equation and reached children. No constructor
contains a price, native trace, or native budget. Return/raise location validity
remains explicit in leaf classification. `ExecutionTrace.sound` checks the
exact evaluator result and successor state.

`StackExecutionTraceNative.ExecutionTrace.bound` proves the recursive compiler
motive by induction on these derivations, using the independent
`stackExecutionCost` as its budget. `StackExecutionTraceRiscV.ExecutionTrace.native`
extracts an actual RISC-V halt within executed Stack cost plus 17, retaining
the original FlattenHyps, target, encoder, native state relation, and oracle tie.
Checks: `stack-execution-native-kernel2`, `stack-execution-trace1`,
`stack-execution-trace-native3`, and `stack-execution-trace-riscv1`; all printed
axioms are standard.

This theorem is conditional on a semantic derivation and local price table.
Completeness for successful compiled guest executions, compiled-program/return
label eligibility, and concrete local price instantiation are NOT yet proved.
The fine Word pipeline and whole-guest gas/input bound are also unfinished, so
this is not yet a source-to-RISC-V finite certificate.

### Scope and code preservation for derivation completeness

`StackExecutionLabelScope` uses the original `getLabelsExact` and
`locCheckExact`. A stored function automatically supplies scope for all its
labels; scope passes to sequence/conditional/loop bodies and call
continuations. In particular, return and handler label literals in a scoped
call are valid without a new per-call artifact computation. The initial tail
entry has no locally introduced labels. All eleven lemmas checked in
`stack-execution-label-scope3` with standard axioms.

`StackExecutionCodePreservation` proves that every eligible leaf preserves the
actual source code map, including normal/final host responses. It then proves
code-map preservation for every semantic derivation by induction, so global
code eligibility and label scope can move to actual successor states. Both
results checked in `stack-execution-code2` with standard axioms.

The remaining completeness proof must construct ExecutionTrace from actual
successful evaluation, using supported post-removal grammar, stored-code
eligibility, label scope, and validity of the final returned/raised location.
These facts are not an assumed trace or native budget. Completeness and the
full finite certificate remain unfinished.

### Atomic derivation completeness

`StackExecutionEligibility` defines the supported post-removal grammar and
valid result forms, including installed returned/raised locations and explicit
exclusion of source Error/TimeOut. It classifies results into the unified
compiler conclusions without changing their source result. Its eight laws
checked in `stack-execution-atomic3`.

`StackExecutionAtomicComplete.executionTrace_atomic` constructs the semantic
derivation from the actual evaluation of every supported leaf. It covers
normal/final FFI, all eight shared-memory operations, returns/raises, and
normal/control/Halt leaves. Invalid result forms are eliminated using the
explicit source result-validity premise. The theorem assumes no derivation,
native trace, price table, or target budget. Checked with standard axioms in
`stack-execution-atomic4`.

Full completeness still requires well-founded assembly over sequence,
conditional, loop, and call evaluations, with stored-code eligibility and
label scope transported through code-map preservation. Concrete compiled
artifact eligibility/prices and the fine Word/source/guest bounds remain
unfinished.

## Source-side cost model (feat/cost-v2-events)

The sections below are the source-side account from the V2 branch (source to Crep, Loop and pre-allocation Word); the sections above are the downstream Word, Stack and native account.

### Accounting rules

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

### Proof obligations

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

### Compiler-induced repeated work

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

### Global source completeness

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

### Return-slot frame epoch

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

### Source-to-Crep executed transfer

`SourceCostCrepWork.CrepWork t p w` counts executed Crep work: one unit per
executed statement and the scalar node work of every evaluated expression,
following the exact evaluator's successor states (selected branch, every loop
guard, actual callee body, matched handler, early failures). Calls also charge
argument words and returned payload words. The removed coarse module
`SourceCostCrepControl.source_crep_executed_work` proved (superseded by the sharp
`SourceCostSharpCrep*` chain), for every exact source `StatementRun` with a non-error result, the four
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

### Seq-free epoch

`Seq` is structural composition with no native operation, so it emits no
event of its own. `StatementRun.seqNext` charges `left ++ right` and `seqStop`
charges `left`. `CrepWork` `Seq` likewise has no local charge (`w1 + w2`, `w1`).
Every executable statement, expression, loop guard, call and size event is
still charged. Without this change, `pan_simp$seq_assoc`, which left-nests
sequences, would pay one extra `Seq` statement per enclosing sequence node on
every early exit. That is a program-size factor. With `Seq` free, association
never changes cost (`SourceCostPanSimpAssoc.simp_seqAssoc_run`).

### Crep-to-Loop executed transfer

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

### Global-access epoch

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

### Sharp replay sites

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

### Installed entry

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

### Whole-program preprocessing

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

### Guest instantiation

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

### Loop to Word

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
| Returning call | 1 + its arguments, plus its return names only when the callee body actually returns a value of that arity with the clock nonzero |
| Other leaves | 1 |

The returning-call price depends on the state. The native return suffix of
`WordToStack` runs only on the return path, so the call pays for it only
there.

The literal `RiscV/WordToStack` lowering ignores Word cutsets, so the price has
no cutset component.

#### Price changes in `LoopWork` and Crep work

A compiled Loop `loop` is `Tick; loop; Tick`. To pay for it, a `LoopWork`
loop iteration now costs 3, and a `CrepWorkP` `while` iteration costs one more
unit. A returning call with a continuation (`callRetCont`) costs 2 instead of 1
in `LoopWork`, paying the call's own unit and the `Tick` after it; the
Crep-to-Loop call proof absorbs this with existing slack. The coarse and sharp Pan-to-Crep `while` proofs absorb this with their
existing slack, so `sharpScore` is unchanged.

#### Production route

The runtime image is built in `RiscV/SourceRuntimeBackendOutput.lean`, lines
40–60. It lowers `panToWordCompileProg loop` directly. `wordProgDCE` there
builds only `discoveryWords`, which are used for FFI-name discovery and are
never lowered. The executed Word code is therefore exactly the
`loop_to_word` output, and no DCE cost step is needed.

#### Pinned Word entry

`GuestCostWordEntry.guest_word_entry` states the guest bound at the Word entry
of the pinned `pan_to_word` `state_rel_imp_semantics`. Its target premises are
those of the pinned theorem. The theorem shows that the entry call
`Call NONE (SOME firstLoopName) [0] NONE`, run from that target at some clock,
does Word work at most `sharpScore ev + 5330`. The proof has three steps:

- `entry_loop_program`: the installed Loop entry is
  `Seq (Call NONE (SOME firstLoopName) [] NONE) Skip`, and `compHOL` of it
  begins with the pinned entry call.
- `entry_loop_word_rel`: the pinned initial Loop–Word relation holds at any
  common clock.
- `guest_source_word` then gives the bound.
