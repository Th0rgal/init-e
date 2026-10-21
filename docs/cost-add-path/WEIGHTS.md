# Source weight retune for the SharpModel route (raise-only)

The checked SharpModel instances (`CrepSharpInstance.selModel`, `CrepSharpTight.tightModel`) price compiled
Crep code at the selector prices: a variable or a constant costs 24, an FFI call `ffiSel` = 121, and so on. A
few source charges were below those prices and are raised. No charge is lowered. Lowering waits for the
combined SSA call-head funding check (lead, 2026-10-21), so the old `loopK` default chain stays valid.

| Charge | Definition | Old | New | Why |
|---|---|---|---|---|
| moved word | `sharpSourceWeights.movedWords` | 14 | 24 | a copied word is a Crep variable read (`copyOk : V ≤ 24`) |
| zero return slots | `slotOverhead n` | 19n | 24n | a slot is a Crep constant (`slotOk`) |
| `raise` of n words | `raiseOverhead n` | 51n + 86 | 51n + 87 | selector raise 87 at n = 0 (`raiseOk`) |
| store of n words | `storeOverhead n` | 112n − 47·[n≥1] | 120n − 48·[n≥1] | `storeWordsCost` at V = 24, O = 48 (`storeOk`) |
| external call | `externalOverhead` (was literal) | 37 | 121 | `ffiSel` (`ffiOk`) |
| call sites | `callSites fn g` | caller+callee table | + `srcTailSitesL` of the callee | Loop tail surcharge `ts` (`CallSitesAligned`) |

Derived constants that changed with these weights:

| Constant | Where | Old | New |
|---|---|---|---|
| one constant global store | `SourceCostGlobalsInit` | 265 | 272 |
| per-global term of `globalsTopInit` | `SourceCostGlobalsTop` | 265 | 272 |
| guest entry additive constant | `GuestCostSourceLoopTop`, `GuestCostSourceWord`, `GuestCostWordEntry` | 25,061 | 25,712 (+7 × 93 globals) |

Replay: every previously green module that depends on `PanStatementWork`, `SourceCostSharpCrepBasis`,
`PanExternalCost`, `SourceSiteMoves`, `TailSiteTable` or `CrepTailSites` was rechecked (checker runs
`rw1`–`rw7`, std axioms only). Nine stale `GuestCost*` copies in this checkout were never green here and
were not replayed; the guest chain is maintained in the guest checkout.

Statement-side prices the model needs, and the slack they would free if lowering is later approved (ADD
path, `CrepModelWalk.lean`): statements 4,466 → 2,834 per ADD (ite 29, store 24, return 15, while 45,
primitive 111, call 195 + cs + ts).
