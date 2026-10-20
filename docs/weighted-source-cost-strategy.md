# Weighted executed-work strategy

The participant target is a native step ceiling of 900,000,000,000. The old affine source-clock proof is unsuitable for this target. No challenge, verifier, or dependency pin changes are part of this strategy.

## Evidence and budget

The removed `CanonicalAffineClosedForm.sourceNativeSlope` multiplied maxima from the Crep, Word, bitmap/removal, named-label and native stages. Its backend factor is 14,467,153. `ActualUnfilteredNativeBudget` identifies that factor as `16 * (bytes.length + 1) + 1`: it scales with the size of the entire submitted image, rather than the locally executed instruction expansion. Source-clock accounting also treats straight-line declarations, expression work and stores as free. Replacing only the source ceiling while retaining these transfer factors cannot give the desired useful bound.

The pinned local `InitE.NatE` and `verifier/check_submission.py` represent finite budgets as arbitrary nonnegative naturals; a 900-billion admission cap was not found there. Treat 900 billion as the required working ceiling regardless of whether enforcement is external or newer than this checkout.

At 200 million gas, 900 billion native steps leaves at most 4500 native steps per gas before initialization and input-dependent overhead. Input work needs its own term: accepted input is at most 134,217,712 bytes. A model must also cover failure/rejection, zero-gas control paths, MMIO and accelerator entry/exit, structured values, stack/register spills, and initialization.

## New proof interfaces

Use a trace of executed source locations or nodes, with local weights. Expressions and flattened word widths contribute to the local node weight. Charge only the selected conditional arm, repeated tests and bodies on loops, actual callees and exception handlers on calls, and actual termination paths. An error/rejection path must retain the work done before it terminates. Never replace a call or loop by an opaque leaf with an assumed cost.

`PanExecutionWork.TraceRun` is the initial exact-HOL-carrier foundation: atomic clauses, sequence continuation/early termination, and selected conditional arms. Its soundness theorem replays into `evaluateHOLFiniteState`. `traceWork` is additive over visited traces and parametrized by local weights; those weights are not yet certified native costs. Declarations, loops, calls, handlers, guard failures and completeness remain to be implemented. The structured `Flapjack.PanCost` evaluator is useful comparison material but is not a replacement for proving a bridge to the authoritative HOL semantics.

For compiler transfer, retain a path-sensitive cost summary per block/call site through each pass. Charge actual expression expansion, flattened copies, stack moves/spills, label/control overhead and emitted native instruction lengths. Compose local simulation costs additively, avoiding repeated multiplication by the largest source body, largest frame or entire image size. The desired final statement is nativeSteps <= initialization + sum(locationVisits * certifiedLocalNativeCost) + explicitly bounded host/MMIO overhead. No numerical coefficient should be adopted before the local compiler proof and artifact check establish it.

## Order of work

1. Instrument all source evaluator clauses and prove erasure/completeness, including terminal outcomes and handlers. Keep existing correctness semantics unchanged.
2. Inspect the final Lab-to-RISC-V proof first: replace the image-size factor by certified local expansion costs. This isolates a concrete source of looseness and sets the target cost currency.
3. Connect local costs backwards through stack, register allocation, Word, Loop and Pancake passes. Preserve per-site information and structured word widths.
4. Reuse established memory/invariant facts, but replace coarse arithmetic ceilings such as 2^64 loop bounds and 2^74 table bounds with actual input/gas/capacity-dependent visit bounds. A finer transfer alone cannot repair such source ceilings.
5. Produce an explicit score below the working ceiling, check the complete certificate, and run the verifier. Measurements guide coefficients and detect omissions; measurements do not prove worst-case bounds.

## Checkpoint and fleet

All three external agents were interrupted and instructed to stop their background work and remain idle. Their terminal reports confirm idle status; no matching worker checker processes remained in the process audit. Do not resume the old fleet tasks without a new explicit root instruction consistent with this strategy.

Old coarse-bound work is preserved on `feat/finite-score` at `80cfbe6af`. The checkpoint includes four checked installed/branch wrappers and an unchecked `MptInsertChoiceStoppedFloorWorld` draft. Revised work is isolated on `feat/weighted-source-cost`. The final finite certificate remains unfinished.
