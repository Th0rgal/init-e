# ADD path cost walk (diagnostic, not a proof)

`AddPathWalk.lean` walks one EVM `ADD` through the pinned guest's Word code at
each compiler stage and prices it with the cost-chain prices. The figures are
diagnostics for choosing contract prices. Nothing here is a checked bound.

## What is walked

The walk covers one `run_frames` loop iteration, the `op_dispatch` call, and
`op_add` with all of its callees: `stack_pop` (twice), `charge_gas`,
`u256_add`, `stack_push` and `pc_add`. Call nodes are charged at the call site,
and each callee body is walked once per call.

Stages come from the real pipeline, applied to
`FrontendStages.Word.outputs` (the Loop→Word output):

| Stage | How it is produced |
|---|---|
| pre-WordSimp | `seqAssoc .skip p` |
| WordSimp-out | `WordSimp.compileExp p` |
| isel | `instSelectExecutable riscvConfig (maxVarHOL p0 + 1) p0` |
| SSA | `fullSsaCcTrans` |
| removeDead | `removeDeadProg` |
| final | `WordBackend.outputs` (allocated) |

## Path witness

Branch decisions are taken from the guest source (`Guest/guest.pp.pnk`) for a
normal `ADD` iteration. They apply only to *compare* IFs. Each Pancake
comparison compiles to a compare IF that materialises 0/1, followed by a test
IF `notEqual v 0`. The walker resolves every test IF statically, using
path-sensitive constant sets with exactly the semantics of `constFpLoop`
(`constFpMoveCs`, `constFpInstCs`, `constFpExp`).

| Function | Decisions | Source conditions |
|---|---|---|
| run_frames | `TEEEE` | `go != 0`; `lds(cur_cont+32) != 0`; `lds(ev+104) == 0`; `pc >=+ len`; `done != 0` |
| op_dispatch | `TTET` | `op <+ 32`; `op <+ 16`; `op == 0`; `op == 1` |
| stack_pop | `E` | `sp == 0` |
| stack_push | `EE` | `sp >=+ cap` (no growth); `sp == 1024` |
| charge_gas | `E` | `gl <+ amount` |

Two self-checks are printed per function:

- at every stage, each function consumes exactly its decision count (`dyn used`);
- every test IF resolves statically (`static`).

The earlier hand-recorded path strings failed both checks. For example, they
sent `run_frames` into an immediate `break`, so earlier totals undercounted.

## Result per ADD

| Stage | Price | Total |
|---|---|---|
| pre-WordSimp | preIselPrice | 14,944 |
| pre-WordSimp | exact isel line bound | 10,456 |
| WordSimp-out | preIselPrice | 14,670 |
| WordSimp-out | exact isel line bound | 10,182 |
| isel | wordOptimizerLocalPrice | 10,182 |
| SSA | wordOptimizerLocalPrice | 15,678 |
| removeDead | wordOptimizerLocalPrice | 13,182 |
| final allocated | wordOptimizerLocalPrice | 10,206 |

The "exact isel line bound" prices each expression node by `lineBound
preAllocLeafBudget` of its own `instSelectExecutable` output.

Not included: the `stack_push` growth path (realloc and `memcpy`).

## Companion checks

- **`WordSimpSurchargeSites.lean`:** counts `dropConsts` constant inserts per
  call site, including repeated `constFp` runs through `simpDuplicateIf`. On the
  ADD path they add +1 each at return labels 499.6 and 499.12. Over the whole
  table: 1,300 sites, 2,576 inserts, at most 18 at one site.
- **`ConstFpExpMonotone.lean`:** checks the 43,794 expressions that
  `constFpLoop` rewrites in the pinned table. Neither `selExpCost` nor the exact
  isel line bound ever increases.

## Running

Each script is elaborated with the source build's `LEAN_PATH` (the
`finite-score-build` packages plus `cost-source-build`), using `lean
--root=submission <file>`.
