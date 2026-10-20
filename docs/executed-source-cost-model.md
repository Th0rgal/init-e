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
events. `executionWork` adds events; `Work.score` takes a dot product with a
coefficient vector. Both compose additively over trace concatenation.
Coefficients must be justified by compiler/runtime proofs; a source unit does
not automatically equal one native instruction.

Each actually executed statement and expression pays one entry event. Children
are charged separately, only the chosen branch runs, and every loop guard
(including the final false guard) is charged. Calls include actual argument
work, body, selected handler/continuation and argument/result copies. Errors,
exceptions, rejections and timeouts retain their executed prefixes.

| Operation | Size accounting beyond entry/children |
| --- | --- |
| Fixed-width arithmetic/comparison/shift | Scalar operation count; numeric magnitude of a 64-bit constant is not a work count |
| Variadic operation | Operand/reduction work, with all evaluator children retained |
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
this definition to `StatementRun`. Compiler/guest bounds should hold for all
such traces; trace uniqueness has not been claimed.

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
| `SourceCostCrepWork`, `SourceCostCrepBasis`, `SourceCostCrepLeaf`, `SourceCostCrepDec`, `SourceCostCrepCall`, `SourceCostCrepHandler`, `SourceCostCrepDecCall`, `SourceCostCrepPrimitive`, `SourceCostCrepAtomic`, `SourceCostCrepControl` | Executed Crep work paid by source events for control paths, declarations, local assignments, stores, returns/raises, calls/declaration-calls, primitive/external/shared operations, including caught exceptions and timeout; return slots paid by requested size | All localized constructors under original state/code/exception/locals relations and non-error result, with program/callee bulk-load premises; preprocessing and Crep-to-Loop transfer remain open |
| `AllocCostModel`, `AllocCostSSA`, `AllocCostPasses`, `AllocCostCompose`, `AllocCostExecuted` | SSA prologue/instruction moves, three-to-two rewrite-site costs, nonamplifying allocation/colouring, and actual path budget for their composed output | Certified straight-line fragments; recursive call/loop reconciliation remains open |
| `AllocCostOptimizer`, `AllocCostCse`, `AllocCostUnreach` | Local static envelopes for must-terminate/dead-code removal, copy propagation, CSE, sequence cleanup and unreachable removal; expansion charged by rewrite sites | Straight-line fragment bounds; grammar/composed optimizer and dynamic control transfer remain separate |
| `AllocCostReconcile`, `AllocCostSSAControl` | Static local syntax envelopes for renaming, reconciliation, loop setup/back-edges, break/continue targets and tail-call argument moves, using actual live sets | Dynamic semantic execution transfer must still charge each occurrence; returning-call composition remains open |
| `SourceCostLoopWork` | Output-indexed exact Loop execution work, soundness and equal-work lifting to a larger clock for non-timeout runs; selected branches, each loop iteration, callees/continuations/handlers exposed | Actual Crep-to-Loop transfer and simplification/live-optimization work proofs remain open |
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
program counters, code and the oracle tie are retained. Branch/call/loop
composition and the bridge from generated expression fragments to these
ordinary blocks remain open.

`SourceCostLoopMark` proves that the actual `markAllHOL` pass preserves exact
Loop work for every trace, including loops and reached handlers/continuations.
The callee code table stays unchanged; only handler/continuation syntax is
marked. `SourceCostLoopCallInputs` and `SourceCostLoopCallPass` prove that the actual
known-label call pass never increases work for any non-error trace under its
original known-labels relation. Indirect-to-direct rewriting retains the same
callee/environment and all body/handler/continuation traces, removing only the
target argument charge; full sequences, branches and loops are covered.
`SourceCostLoopLiveLeaf` checks all atomic liveness cases under the original
locals-projection premise. It reuses existing semantic correctness for the
actual successor/locals relation and proves the retained-or-deleted statement's
local cost does not increase. The remaining liveness composition covers
sequences, branches, loops and returning calls; full `optimiseHOL` still needs
that transfer to close the installed-callee gap.

## Remaining end-to-end obligations

1. Execute-cost transfer through source preprocessing and Crep-to-Loop. The
   localized source-to-Crep statement transfer is checked for non-error runs
   under original semantic relations and explicit bulk-load premises.
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

Liveness control checkpoint: SourceCostLoopLiveBase factors the original
result-indexed locals relation and uses semantic correctness only to identify
the output of an independently constructed costed target trace. Sequence,
branch, mark, and all four loop-exit constructors now preserve or decrease
actual executed work. Loop fixed-point metadata is derived from the actual
shrink compiler, not assumed. SourceCostLoopLiveCall preserves successful
argument reads and reuses unchanged callee traces exactly for tail calls and
returning calls without handlers. Handler/continuation composition, early call
exits, and the global liveness induction remain open; LoopOptimiseWork is not
yet discharged. These facts introduce no final native coefficient or score.
