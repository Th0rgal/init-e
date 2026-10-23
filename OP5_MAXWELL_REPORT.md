# Op 5 — working report

Status: COMPLETE for Op5 compiler-domain extension. Final verification passed.
The earlier checkpoint sections below are historical and superseded by the final
integration section. This report does not claim completion of Challenge C.
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

## Fifth checkpoint: full initializer correctness and semantic simulation

InitCorrectArena.lean now generalizes the complete pinned initCodeThm proof,
not merely the successful-run projection. Under initCodePreWithArena and all
original compiler guards, it derives normal execution, all original pointer
register facts, the actual stateRelHOL from the arena-extended reduction to the
physical poststate, FFI preservation, initPropWithArena at the computed limits,
ordinary/shared domain preservation and initial/final memory agreement across
the entire enlarged source domain.

The proof keeps the old scalar reducer T0 for pointer/store/stack calculations.
It proves the original heap assertion is H, identifies the scratch assertion
from actual preserved reads, derives old-heap/scratch domain disjointness from
separated ownership, and merges H * scratch into the enlarged memoryHOL.
The relation proof retains bitmap/data, store and physical stack factors.
There is no extra interval hypothesis, successful-run premise, postrelation
premise or unproved simulation assumption.

MakeInitArena.lean implements optional and total arena-aware constructors.
makeInitOptWithArena_correct proves the optional constructor returns a state
in the actual StackRemove relation and satisfies initPropWithArena, using the
full new initializer theorem. The total fallback retains arena ownership and
all original fallback fields; its behavior is not used to conceal a failed
optional initialization in this theorem.

InitSemanticsArena.lean proves entry-wrapper semantic equality via the pinned
initializer clock-shift theorem, then composes the new successful initializer
relation with the existing CompileSemantics.compileSemantics theorem.
makeInitOptWithArena_semantics establishes that non-failing semantics of the
arena-aware initialized Stack program equal semantics of unchanged compiled
entry code. This closes the StackRemove initialization/simulation layer.

Verification: all three files pass whole-file Lean and turbo-lean check. The
four theorem specifications (one InitCorrectArena, one MakeInitArena, two
InitSemanticsArena) all audit ok=true with empty warnings and shadowed-constant
lists. Printed axioms are confined to propext, Classical.choice and Quot.sound
(`choice` is pretty-printed unqualified inside MakeInitArena's open Classical).
No sorryAx. No Boss-only record command was run.

Remaining: adapt the fullMakeInit pipeline and its Lab-side machine assumptions,
then derive the Word initializer union domain and apply PanToWord/assembly with
that domain. The complete goal is still not achieved. This turn is progress:
it adds a checked full initializer simulation theorem rather than restating
an intended bridge.

## Lab initialization semantics checkpoint

Added InitPipelineArena.lean: propagateTheseWithArena retains the full pinned
machine guard bundle and adds independently owned memoryHOL scratch alongside
bitmap/data ownership. makeInitSemanticsWithArena derives actual optional
initialization success and non-failing semantics from that bundle and the
unchanged dischargeThese compiler bundle. No execution or postrelation is
assumed.

Added LabInitArena.lean: memoryAssumptionWithArena and labAssumptionsWithArena
retain all Lab guards and replace only the ownership assertion with its
arena-framed version. propagateThese_s2_withArena transports memory, domain,
headers and renamed registers through the actual unchanged s2 constructor.
dischargeThese_s2_withArena discharges the original compiler-side bundle.
The label/code, call-argument, actual s3 state relation and Lab entry-location
proofs were generalized to the new assumptions. stageLab_withArena composes
actual StackNames and StackToLab simulation without requiring the old
contiguous memory assertion. lab_init_semantics_withArena proves optional
arena initialization succeeds and non-failing semantics of its result equal
semantics of the unchanged compiled physical Lab entry.

Verification: both new files pass whole-file Lean; LabInitArena also emits its
olean. turbo-lean check verifies both files. JSON audit-spec reports ok=true,
one tight specification for InitPipelineArena and ten for LabInitArena, zero
vacuous specifications, and empty warnings, horizontal-packing and
shadowed-constant lists. All five printed Lab theorem axiom sets and the
pipeline theorem contain only propext, Classical.choice and Quot.sound;
no sorryAx. No Boss-only record command was run.

Remaining: complete the StackAlloc/rawcall portion and arena-aware total
fullMakeInit constructor, then thread the resulting Word union domain into
Pancake/assembly integration. The full compiler-domain goal remains active
and is not claimed complete. This checkpoint closes the Lab-to-initialized
StackRemove semantics portion under the new memory contract.

## Full initializer and Word/Pancake union-domain checkpoint

FullInitArena.lean adds fullMakeInitWithArena, composing the unchanged actual
Lab, StackNames and StackAlloc constructors with the arena-aware optional and
total StackRemove constructors. fullMakeInitWithArena_semantics proves the
optional result is present and the non-failing semantics of the complete
initialized source equal physical compiled Lab entry semantics. The proof
composes rawcall and StackAlloc simulation with the prior Lab/Names/Remove
bridge. Successful optional initialization exposes the actual arena reduction
and initPropWithArena; no fallback behavior or successful-run premise hides
initialization failure.

AssemblyInitArena.lean carries the full actual initializer theorem through the
Lab s2 state, including original pointer/register bounds, the actual
StackRemove relation, FFI, shared domain, and memory agreement over the entire
arena-extended initialized domain. It also exposes the actual reducer returned
by successful fullMakeInitWithArena.

WordInitArena.lean proves the Word initializer domain is exactly the original
heap addresses union arena, with the original scalar pointer/alignment bounds.
It derives the CurrHeap and HeapLength store facts, FFI/endianness/shared domain,
and memory agreement with the original Lab memory on every address of the
union. It uses the actual unchanged WordToStack initializer; domain transfer
is not a separate assumed relation.

PanToWordArena.lean applies the existing general Pancake-to-Word simulation to
that initialized Word state with Pancake memaddrs equal to persistent heap
addresses union arena. The global reservation is split out of the persistent
part while scratch remains ordinary source memory. The explicit arenaAligned
premise is needed for the new domain's word values, in addition to the pinned
persistent base alignment. panToWordStageLabWithArena derives the target-state
memory/register facts from the actual LabToTarget.makeInit, mcConfOk and
goodInitState contracts, retaining the original machine-side guards.

Verification: all four new modules pass whole-file Lean and emit oleans.
FullInitArena, AssemblyInitArena, WordInitArena and PanToWordArena pass
turbo-lean check and JSON audit-spec with respectively 2, 2, 5 and 3 audited
tight specifications; all ok=true with empty warnings, horizontal packing and
shadowed-constant lists. Printed theorem axioms are only propext,
Classical.choice and Quot.sound. No sorryAx or added axiom. One earlier
PanToWord check ran against a pre-fix source with missing scoped Classical;
it failed, was corrected, and the final source passed. No Boss-only record
command was run.

Remaining: generalize EncodingInitState/WordToStack initialization contracts,
the machine installation-to-Lab assumption derivation, and the final
AssemblyLabChain/AssemblyTop compiler theorem to invoke these new union-domain
constructors and bridges. Full compiler integration is still unproved, so the
goal remains active. Frozen InitE source semantics and pinned constants were
not modified.


## Final integration and completion audit

The formerly remaining integration is now implemented in:

- EncodingInitArena.lean and WordToStackInitArena.lean: the actual WordToStack
  initStateOk contract, bitmap/code/GC facts, and Lab/Stack semantics link are
  derived from successful arena-aware full initialization. No contiguous-domain
  assumption is reintroduced.
- MachineMemoryArena.lean and MachineAssumptionsArena.lean: derive the entire
  Lab initializer assumption bundle from actual machine initialization memory,
  configuration/header/bitmap guards, and separate scratch ownership.
- MachineLabArena.lean: applies the actual LabToTarget.semanticsCompile theorem
  to the enlarged physical ordinary domain.
- LabChainArena.lean: composes actual Pancake/WordToWord/WordToStack/StackToLab
  simulation and derives successful arena-aware full initialization.
- ResourceArena.lean and LabResourceArena.lean: retain the original stack-depth
  and readLimits resource flag, deriving its safe-for-space implication for the
  enlarged initial state.
- CompileSemanticsArena.lean: compileSemanticsWithArena proves the complete
  compileProgMax-to-machine-semantics theorem. Its input interface is
  compileSemanticsWithArenaStatement, the full pinned hypothesis list with
  generalized installation and ordinary source domain. It concludes the same
  extendWithResourceLimitPrimeHOL result using the original optionLt/readLimits
  flag. It assumes no successful initializer run, intermediate compiler
  relation, memory-preservation theorem, or desired observable semantics.
- ArenaLayouts.lean: proves the pinned ordinaryDomain is its aligned persistent
  byte interval; guestDomain is exactly ordinaryDomain union guestWordArena;
  pinned scratch lies below sourceBase, satisfies the machine heap-separation
  guard, and its byte arena is closed over all bytes of aligned words. The
  requested numeric interval is proved already contained in ordinaryDomain at
  this pinned revision.

The byte/word distinction is explicit. byteArena is the full physical byte
predicate passed to panInstalledWithArena/goodInitState. arena is the aligned
word-cell predicate. The first new top-level guard is
arena a iff byteArena a = true and holByteAligned a = true. The second excludes
arena from the entire machine initialization interval [lenReg,len2Reg), which
contains the persistent heap, globals, initializer store and physical stack.
Bitmap exclusion is derived from the strengthened installation contract. This
separation is proved for the pinned below-base guest scratch; it is not assumed
silently by treating aligned word starts as a byte-complete physical domain.

The generalized theorem applies to all supported targets (and therefore
RISC-V) through the actual MachineConfig target semantics. FrameBridge.lean
provides the explicit WordToStack domain transport, target code/buffer frame,
and eight-byte cell preservation for stack-confined target writes. The pinned
and requested concrete stack separation theorems remain in MemoryDomain.lean.

Read-only advisor audit of the final interfaces found no material specification
gap for Op5's compiler-domain extension. The audit expressly distinguishes
this result from constructing a concrete executable guest installation or
completing Challenge C. Frozen InitE source semantics, guest layout, compiler
code generation, and the pinned Flapjack package sources are unchanged.

Reproduction from this worktree (ELAN_HOME=/var/lib/sandboxed-node/.elan):

    turbo-lean --json audit-spec submission/InitECandidate/Proofs/Op5/CompileSemanticsArena.lean
    turbo-lean check submission/InitECandidate/Proofs/Op5/CompileSemanticsArena.lean
    lake env lean submission/InitECandidate/Proofs/Op5/CompileSemanticsArena.lean

Imports require their ordinary Lean oleans; this worktree contains the checked
module artifacts. OP5_VERIFICATION.json records per-source SHA-256, complete
specification-audit results, verifier exit codes and outputs for every Op5 Lean
module. OP5_AXIOMS.txt records the final theorem and frame/layout axiom audit.
These are verification records, not a Boss certification or governor receipt.
No maxwell record or research-governor record command was run.


### Verified acceptance evidence

| Requirement | Current authoritative evidence |
| --- | --- |
| Locate contiguous restriction | Exact restriction locations above; frozen SourceSemantics/Installed/PanInstalled/CompileSemanticsStatement inspected at baseline 4cb9619cd6. |
| Generalize installation/domain | installedWithArena, panInstalledWithArena, twoRegion, compileSemanticsWithArenaStatement and the proved compileSemanticsWithArena. |
| Preserve the actual compiler chain | Checked initializer, Lab/Stack/Word/Pancake and resource-limit modules imported transitively by the final compiler theorem. |
| Scratch/persistent/stack separation | regions_disjoint, guest_scratch_persistent_disjoint, guest_stack_disjoint, requested_stack_disjoint, guestArena_machine_separation. |
| Word/Stack and target frame bridges | wordToStack_twoRegion, target_code_frame, target_stack_preserves_cell over actual MachineConfig target bytes. |
| Concrete source and requested layouts | ordinaryDomain_interval, guestDomain_union, guestByteArena_word_closed, requested_union_ordinaryDomain. |
| 0 sorryAx | OP5_AXIOMS.txt: final theorem dependency closure uses only propext, Classical.choice and Quot.sound; frame/layout closures use subsets of these. |
| turbo-lean audit/check | OP5_VERIFICATION.json: all 30 current Op5 modules pass both commands; all 73 audited theorem specifications are tight, with zero warnings or vacuous/trivial specifications. Source SHA-256 values match current files. |
| Branch, report and reviewable result | All implementation and records committed on op5-flapjack-scratch; no package or frozen challenge semantics edits. |
| Boss-only commands | No maxwell record or research-governor record was invoked. |

The compiler-domain extension itself is now fully integrated and proved.
The theorem remains conditional on actual compiler configuration, successful
compilation, generalized installation and the original source-program guards,
as is the pinned compiler correctness theorem. This operation does not produce
a concrete guest installation witness, prove guest program non-failure, or
claim the full Challenge C submission. The operation brief's numeric layout
mismatch remains explicit: its requested interval is already inside the old
ordinaryDomain at this revision; the authoritative guest's actual below-base
scratch is the nontrivial new region handled by the extension.
