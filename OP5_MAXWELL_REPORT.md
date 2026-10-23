# Op 5 — working report

Status: IN PROGRESS. No end-to-end compiler-domain extension is claimed.
Branch: op5-flapjack-scratch; starting revision 4cb9619cd6.

## Authoritative layout discrepancy

The operation brief describes scratch [0xa1001000,0xa1c00000) below
sourceBase. At the prepared revision, InitE/Parameters.lean instead defines
sourceBase=0xa1000000, scratchStart=0xa0411000, scratchEnd=0xa0fff000,
and globalsWords=67. Guest/Model.lean agrees on scratchBase=0xa0411000
and heapBase=0xa1000000. The prose memory-layout table in docs/CHALLENGE.md
contains a different layout (including 93 globals) from these Lean constants.
The requested scratch range is therefore above sourceBase and already inside
the existing contiguous ordinary region at this revision.
Do not change frozen challenge semantics to conceal this discrepancy.

## Exact restriction locations

* InitE/SourceSemantics.lean: ordinaryDomain is StackRemove.addresses
  sourceBase ((stackStart-sourceBase)/8-globalsWords).
* Flapjack/Compiler/Backend/Semantics/TargetSem/Installed.lean: installed
  existentially chooses the assembly state and defines heapStackDm by the
  unsigned half-open register interval [t.regs regs.1,t.regs regs.2).
  goodInitState receives heapStackDm || bitmapsDm. The bitmap separation
  assertion means bitmapsDm cannot simply absorb arbitrary scratch storage.
* Flapjack/Pancake/Proofs/PanToTarget/PanInstalled.lean: panInstalled repeats
  that interval and adds agreement with the source memory on pDom.
* Flapjack/Pancake/Proofs/PanToTarget/CompileSemanticsStatement.lean: the
  top-level compiler theorem separately requires s.memaddrs =
  StackRemove.addresses (getReg mc.lenReg) (heap_len-globals_size).
  Changing installed alone is insufficient.
* Flapjack/Compiler/Backend/WordToStack/Proofs/StateRel.lean: stateRel
  requires t.memory=s.memory and t.mdomain=s.mdomain. These conjuncts are
  domain-shape agnostic.
* Flapjack/Compiler/Backend/StackRemove/Proofs/StateRelation.lean: stateRelHOL
  uses separation-logic memory over source.mdomain alongside stack storage.
* Flapjack/Compiler/Backend/LabToTarget/InstFrame.lean: stateRel_frame
  requires byte agreement on the aligned source domain and preservation
  outside it; bytesInMem_frame handles code/buffer preservation.

All Flapjack paths above are relative to .lake/packages/flapjack.

## Implemented contracts and bridges

* MemoryDomain.lean: generic aligned two-region domain, stack disjointness,
  stack-write frame, concrete pinned and requested layouts.
* Separation.lean: exact separation-logic splitting of memoryHOL over a
  disjoint union, and union-domain stores preserving an arbitrary compiler
  stack/bitmap frame using the pinned MemoryWrites.memoryWrite theorem.
* Installation.lean: installedWithArena keeps every pinned installed clause,
  extends the ordinary byte domain by arena, and strengthens bitmap exclusion.
  installedWithArena_empty proves exact compatibility with installed.
* PanInstallation.lean: panInstalledWithArena uses the same memory/domain
  witness and proves implication to installedWithArena.
* FrameBridge.lean: transports the two-region word domain through the actual
  WordToStackProofs.stateRel; applies the actual LabToTarget bytesInMem_frame
  theorem to the union byte domain; proves preservation of all eight bytes of
  source cells under stack-confined updates using MachineConfig.target.getByte.

All modules live in submission/InitECandidate/Proofs/Op5. None edits frozen
challenge semantics or the pinned package checkout.

## Verification and cache correction

The prewarmed InitE/Parameters.olean was copied from evm.fast-dev and did not
match this revision's source. Its trace retained that original path. Rebuilt
InitE.Parameters with lake build before accepting subsequent proof results.
This matters: a previous check falsely rejected scratchEnd <= sourceBase
because it had imported different constants. All current proofs use the
rebuilt parameter module.

MemoryDomain, Separation, Installation, PanInstallation and FrameBridge each
passed whole-file Lean checking with explicit #print axioms outputs restricted
to propext, Classical.choice and Quot.sound. No sorryAx appears in these outputs.
The turbo-lean check results have also verified the modules (final formatting
edits to Separation/FrameBridge are rechecked before commit).
Each module was passed to turbo-lean --json audit-spec. The first FrameBridge
audit reported a false binder-shadowing match on an unqualified domain
application; qualifying the constant addresses that parser ambiguity without
changing the theorem. Final audit summaries are recorded below after inspection.

## Remaining work (goal not complete)

The generalized installation contracts are not yet threaded into the full
Pancake-to-target compiler simulation. In particular AssemblyPanToWord,
AssemblyLabChain and top-level compiler contracts retain their contiguous
addresses equality. The new frame bridges do not alone eliminate this equality.
The actual source/guest scratch gap remains until that integration is complete.
The requested arena differs from the pinned source layout as described above;
the generic contracts deliberately support both without altering the challenge.

No maxwell record or research-governor record command was run.

### Final audit results for this checkpoint

| Module | Specifications | audit-spec ok | turbo-lean check |
| --- | ---: | --- | --- |
| MemoryDomain | 7 | true | verified |
| Separation | 2 | true | verified |
| Installation | 1 | true | verified |
| PanInstallation | 1 | true | verified |
| FrameBridge | 3 | true | verified |

All five final audit outputs have empty warnings and shadowed_constants lists.
Checks used `turbo-lean check submission/InitECandidate/Proofs/Op5/<module>.lean`;
audits used `turbo-lean --json audit-spec` with the same paths. The whole-file
checks used `lake env lean` under the v4.33.1 toolchain. The allowed axiom union
is {propext, Classical.choice, Quot.sound}; it excludes sorryAx.
