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

## Second checkpoint: StackRemove ownership lift

Added HeapExtension.lean and StackRemoveArena.lean. memory_frame_extend proves
that an arbitrary compiler frame survives extension of both memory graphs by
an arena outside the complete old target domain, with source/target value
agreement on that arena. This is a full function-graph separation theorem,
not just a domain subset or pointwise read property.

stackRemove_stateRel_withArena applies it to the actual stateRelHOL. All
26 outer clauses and the complete five-factor separated heap are retained.
The proof reassociates the pinned separation assertions and extends the
ordinary source and physical target domains together. It assumes neither a
postrelation nor successful compiled execution. initReduceWithArena adds only
the arena domain to the original reduction state; all original fields remain.

Both new modules pass turbo-lean --json audit-spec (ok=true, one theorem each,
no warnings or shadowed constants) and turbo-lean check. Whole-file checks
reported allowed axioms only: memory_frame_extend uses propext and Quot.sound;
stackRemove_stateRel_withArena additionally uses Classical.choice. No sorryAx.

### Exact next integration boundary

InitReduce.initReduce line 49 overwrites mdomain with contiguous heap words.
InitProp.initProp ends in exact ownership of two wordListExists regions.
InitCodePre.initCodePre similarly exactly owns bitmap/data plus heap/stack,
so it rejects an input domain already containing an independent scratch arena.
The next step is to generalize InitCodePre/InitProp with an arena frame and
prove unchanged initCode execution preserves that frame. Merely invoking the
old initCode theorem on an enlarged domain is invalid. The old
InitCodeCorrect.initCodeThm already tracks a frame H in its internal proof;
that frame must be reflected in the generalized input/output predicates.
Then makeInitOpt/Any, fullMakeInit, and AssemblyInitMemory can carry the union
into the already domain-generic panToTargetPanToWordStage.

A read-only advisor confirmed this route; no implementation was delegated.
The original full goal remains incomplete and active.

## Third checkpoint: initialized-state predicate and actual initializer execution

Added InitPropArena.lean: initPropWithArena retains every one of the pinned
32 initialized-state clauses, with a separately owned scratch graph alongside
the two heap regions. initProp_withArena constructs this predicate from the
pinned predicate and a domain-disjoint arena via assertion_arena_extend.

Added InitializerStores.lean: initializer_terminal_write proves the initializer's
terminal stack-slot write preserves scratch heap ownership. The
storeListCode_preserves_arena theorem derives a successful evaluation of the
actual unchanged storeListCode and preservation of all arena values. Its input
is separated heap ownership and the original register/domain guards, not a
successful evaluation or a supplied poststate relation.

Added InitializerExecution.lean: runInitCode_preserves_arena applies the actual
unchanged full initCode execution theorem. It retains all original register
outcomes, the complete output heap assertion and the poststate shape, and
proves every arena value unchanged. Its input heap is stated after the terminal
stack-slot write, matching the pinned execution theorem; the preceding
initializer_terminal_write establishes that heap from separated initial
ownership. This is not yet the full generalized initCodeCorrect.initCodeThm:
the derivation of this execution input and the enlarged stateRelHOL/InitProp
from the generalized installation/precondition still needs integration.

All three new files pass whole-file Lean checks and turbo-lean check. Their
specification audits report ok=true with no shadowed constants or warnings
(after line wrapping the final InitializerExecution signature). They add six
theorems in total. Printed theorem axiom unions remain confined to propext,
Classical.choice and Quot.sound. No sorryAx is used.

Next: derive the arena-framed initializer input heap from an arena extension
of InitCodePre, then construct the generalized optional initializer and thread
its simulation through fullMakeInit and the PanToWord assembly boundary.
The end-to-end operation remains incomplete; no record command was run.

## Fourth checkpoint: derive initializer execution from full precondition

InitPreArena.lean defines initCodePreWithArena with all pinned register,
header, flag, alignment and capacity guards, and exact ownership of the
bitmap/data region, contiguous initialization region and independent scratch
heap. initCodePreWithArena_run derives successful evaluation of the actual
unchanged initCode, its exact poststate shape, and preservation of every arena
value directly from that precondition and the original maxHeap bound.

The proof derives pointer layout, heap/stack splitting, the five header
permissions and final stack-slot permission from the owned memory graph. It
then derives the terminal write and store-list input heap, executes the
pinned runInitCode, and reads scratch preservation from the retained frame.
It does not assume successful execution or the lower-level execution heap
used by the previous checkpoint.

HeapExtension.lean also adds memory_domains_disjoint, deriving address-domain
non-overlap from separated function graphs. This theorem uses no axioms.
It will permit reconstructing the enlarged state relation without adding
an unnecessary concrete interval-separation hypothesis.

Verification: InitPreArena passes whole-file Lean checking and turbo-lean
check; its one specification audits ok=true, no warnings or shadowed constants.
HeapExtension passes both checks and its two-specification audit has the same
clean result. initCodePreWithArena_run has only propext, Classical.choice and
Quot.sound dependencies. No sorryAx. The prior turn constituted progress;
this checkpoint adds new checked execution evidence and is also progress.

Remaining integration is still substantive: construct full stateRelHOL and
initPropWithArena for the actual post-initializer reduction from this framed
precondition, rather than only prove execution/value preservation. Then adapt
makeInitOpt/Any and fullMakeInit, derive the union Word initializer domain,
and thread into the compiler assembly. The read-only advisor identified that
all scalar lemmas of InitCodeCorrect can remain unchanged, while its memoryHOL
identity must become H * scratch and its final ownership proof reassociated.
No Boss-only record command was run; full goal remains active.
