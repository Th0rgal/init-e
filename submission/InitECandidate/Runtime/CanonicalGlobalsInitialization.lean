import InitECandidate.Runtime.CanonicalGlobalsInitialRelation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

theorem baseline_global_declarations_kind :
    FrontendStages.Declarations.globalDeclarations.all isDeclHOL = true := by decide_cbv

theorem baseline_global_declarations_words :
    ((decShapesHOL FrontendStages.Declarations.globalDeclarations).map sizeOfShapeHOL).sum =
      globalsWords := by decide_cbv

/-- Actual source declaration evaluation produces the generated initializer
run over canonical installed memory, preserving its original state relation. -/
theorem canonical_globals_initialize (input : Guest.InputBlob)
    (sourcePost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceRun : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      (canonicalGlobalsSourceState input)
      (fun address => Classical.propDecidable ((canonicalGlobalsSourceState input).memaddrs address))
      FrontendStages.Declarations.globalDeclarations = some sourcePost) :
    ∃ initialized, evaluateHOLFiniteState (canonicalPanEntryState input)
        (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized) ∧
      panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalContext sourcePost initialized ∧
      initialized.clock = (canonicalPanEntryState input).clock ∧
      initialized.ffi = (canonicalPanEntryState input).ffi ∧
      initialized.locals = (canonicalPanEntryState input).locals ∧
      panGlobalsByteAlignedHOL FrontendStages.Declarations.globalContext.globalsSize := by
  classical
  apply PanGlobalsInitGlobalsAssembly.initGlobalsAll (canonicalGlobalsSourceState input)
    FrontendStages.Declarations.globalDeclarations FrontendStages.Declarations.globalInitial
    sourcePost FrontendStages.Declarations.globalInitializers [] []
    FrontendStages.Declarations.globalContext (canonicalPanEntryState input)
    (Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 heapEnd) globalsWords)
  refine ⟨sourceRun,List.all_eq_true.mp baseline_global_declarations_kind,
    FrontendStages.Declarations.compileGlobals_eq,canonical_globals_initial_relation input,
    ?_,?_,?_,?_,rfl,?_,?_⟩
  · rw [baseline_global_declarations_words]
    change _ = Compiler.Backend.StackRemove.addresses
      ((canonicalPanDeclarationState input).topAddr - panBytesInWord 64 * BitVec.ofNat 64 globalsWords - 0)
      globalsWords
    rw [canonical_pan_source_top]
    simp only [BitVec.add_sub_cancel,sub_zero]
    rfl
  · exact baseline_globals_disjoint
  · intro address valid
    change (canonicalPanDeclarationState input).memaddrs address
    rw [canonical_pan_memory_domain_split]
    exact Or.inr valid
  · exact PanGlobalsCompileTopSemanticsDecls.alignedZero
  · intro name shape address present
    exact (Bool.noConfusion present.1)
  · rw [baseline_global_declarations_words]
    exact baseline_globals_size_fits

#print axioms baseline_global_declarations_kind
#print axioms baseline_global_declarations_words
#print axioms canonical_globals_initialize
end InitECandidate.Runtime
