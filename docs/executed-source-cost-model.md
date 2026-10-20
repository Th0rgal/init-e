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

## Checked compiler pieces

| Stage/modules | Proven result | Scope/remaining obligation |
| --- | --- | --- |
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
this sharper ordinary-instruction charge. Conservative control-line charges
remain pending their analogous refinement.

## Remaining end-to-end obligations

1. Full executed source-to-Crep/Loop statement transfer, including preprocessing,
   calls, handlers and failure prefixes, with original semantic relations.
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
