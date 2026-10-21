# finite-auth handoff (2026-10-21, user stop request)

Branch `feat/cost-v2-events`, revision `1cd21fbf8f7344fdbb60b8b5911f5f96a2266797` (pushed). No
uncommitted work, no background builds or watchers.

## Checked (std axioms only)

The manifest is `work/cost-source-build/logs/phaseC-manifest/modules.txt`: 103 modules, each with the
checker run that last checked it. The runs are `rw1`–`rw7` (weight replay) and `fin1` (the new or changed
model modules); their logs are under `work/cost-source-build/logs/<run>/`.

- **Raise-only weight retune.** The old/new table is in `WEIGHTS.md`. The guest entry constant is now
  25,712. Every previously green dependent module was replayed.
- **Width certificate** (`CrepSharpWidth`, `GuestWidth.guest_inputs_width`): covers all 826
  `pan_to_crep` inputs.
- **Generic model.**
  - `CrepSharpModel` through `CrepSharpLoop`: `SharpModel.source_loop_work`.
  - Instances: `CrepSharpInstance.source_loop_sel_work` and `CrepSharpTight.source_loop_tight_work`.
- **Phase C pieces.**
  - `CrepSimpIdem.crepSimp_idem`
  - `CrepErase.nodeT_erase`
  - `CrepErase.crepSimp_erase`
  - `PanSourcePriceT.sourcePriceT_compile`: the source charge exactly equals the `tightP` total of
    what `pan_to_crep` emits.

## Unverified or diagnostic only

- **ADD figures from the walkers** (`SsaWalk`, `SsaSiteWalk`, `CrepModelWalk` in this folder).
  - Pre-SSA tight-model Crep work: 13,447 per ADD after the charge switch; 16,482 with today's `srcK`
    charge.
  - The SSA stage adds 5,496 per ADD.
- **Call-site alignment** for the canonical table is empirical only (scratch `align.lean`): 825/826
  labels match, and the generated entry `main` (label 64) has empty tables.

## Open issues

1. **Expression-charge switch** to `sourcePriceT` (not done). It breaks the old `loopK` chain, so it
   needs the lead's decision on retiring that chain.
2. **`CallSitesAligned` certificate.** The existing name-distinctness proof needs raised limits, so a
   chunked route is required.
3. **Width and context premises at the entry.** `VarsSmall`/`FuncsSmall` for the entry context and
   `CodeWidth` for the code table still need to be connected to `guest_inputs_width`.
4. **SSA call-head funding** (lead and finite-claude4).
5. **Retiring the old SharpCrep modules.** About 15 helper lemmas must move first.

## Restart

Check modules with `python3 work/cost-fleet-check.py source <log> <ModuleStems...>`, run from
`trim-space/init-e` with bare module stems, listing changed dependencies first. Never raise limits.
