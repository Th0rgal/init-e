# Executed-cost theorem audit

The target is an input-uniform RISC-V step ceiling at most 900,000,000,000.
A finite bound with an enormous coefficient is insufficient. The retained
approach charges executed source expressions/statements and actual operation
sizes, then proves local compiler expansion bounds.

| Theorem family | Assessment | Action |
| --- | --- | --- |
| `PanCostTotal`, `PanStatementWork`, `PanTotalExpressionCost` | Total traces follow actual evaluation; suitable basis for guest work bounds. Trace existence alone supplies no numerical ceiling. | Keep. |
| `PanLayoutCost`, `PanBulkExpressionCost`, `GuestBulkLoadApplicability` | Local context/layout premises and size-dependent loads; the guest load-site certificate discharges the six-word restriction. | Keep and compose. |
| `CrepToLoopLocalBound`, `LoopExecutedWork`, `LoopToWord*Work` | Local expression expansion and executed generated code; small coefficients without whole-program maxima. | Keep. |
| `WordPullWork`, `WordSelectionWork`, `WordSelectedPathCost` | Full selector preprocessing and actual selected paths; bounds scale with expression work. | Keep. |
| `WordPathWorkCorrect`, `StackPathWorkCorrect`, `StackRemovePathWorkCorrect` | Full semantic/compiler simulations with actual-successor budgets and original relation/resource premises. | Keep; replace coarse analytic caps around them. |
| `WordNativeInstructionCost`, `StackStraightLineCost` | Explicit local reload/spill bounds independent of total frame size. | Keep. |
| `LabWeightedInstructionTrace`, `LabWeightedMixedTrace`, `LabLocalWork` | Charges executed instruction expansions; avoids multiplying by total ROM bytes. | Keep and connect to the preceding stages. |
| Guest memory ownership, frame, gas monotonicity, progress, input-domain and geometry proofs | Useful semantic premises and iteration/size bounds, even when expressed using the old clock. They do not by themselves bound new expression/statement work. | Keep; reuse premises when proving executed work. |
| Whole-program size ceilings and source-clock affine products | Too coarse for the target. Some are still imported by initialization/geometry modules, so their absence of utility cannot be inferred from their names. | Remove isolated wrappers now; separate mixed dependencies before further deletion. |
| Generic finite-certificate / bootstrap / behavior matching lemmas | Logical interfaces remain useful with a new quantitative transfer. | Keep. |

## Removed

Removed these seven modules, 329 source lines, as a dependency-closed obsolete
wrapper set: `BaselineFiniteCertificate`, `BaselineSourceAffineTransfer`,
`BaselineStackPathAffine`, `CanonicalAffineClosedForm`,
`CanonicalOriginalNativeAffine`, `ExpandedMainFiniteCertificate`, and
`StackRemovePathAffineSimulation`.

They instantiate global code-size/bitmap/ROM bounds or package their oversized
source-clock product into a conditional finite certificate. None adds a needed
local execution lemma. In particular the closed source-to-native formula used
14,467,153 as its native factor before multiplying other stage maxima.
The old conditional finite certificate was never a finite submission.

All retained participant Lean imports were scanned after deletion: no imports
of the removed modules remain. The new native instruction/path proofs passed
Lean and the axiom audit before this cleanup. Deletion does not modify the
challenge or the submitted binary/certificate. Removed sources remain available
in Git history; no compatibility re-export or archive copy is retained.

Further cleanup should detach useful initializer/state definitions from old
coarse endpoint imports, then delete the resulting unused coarse subgraph.
Do not delete semantic geometry merely because an import path reaches an old
bound. The final guest executed-work bound, full RISC-V transfer, and finite
certificate remain outstanding.
