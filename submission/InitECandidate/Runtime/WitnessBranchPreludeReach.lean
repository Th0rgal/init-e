import InitECandidate.Runtime.WitnessBranchPrefixFrame
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.WitnessExtensionStoresProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem occupancy_locals {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s witnessBranchOccupancyUpdate).2.locals = s.locals := by
  rw [source_witness_branch_occupancy_fragment,evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
    · exact (evaluate_store_control_frame s _ _).2.1
  · rfl

private theorem prefix_globals (program : ProgHOL 64)
    (supported : ∀ watched, avoidsGlobalAssignment watched program = true) : OriginalGlobalsFrame program :=
  originalGlobalsFrame_leaf program supported

/-- Both actual pre-dispatch stores either reject or reach the index increment
without source-clock cost. Every other word, local, global and domain is retained. -/
theorem witness_branch_prelude_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top branch index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (code : s.code = originalRuntimeCode) :
    Reaches s (witnessBranchAt 2)
      (fun next => next.locals = s.locals ∧ next.globals = s.globals ∧ next.code = s.code ∧
        next.memaddrs = s.memaddrs ∧ next.be = s.be ∧
        ∀ watched : BitVec 64, watched ≠ branch+32+index*8 → watched ≠ top+40 →
          next.memory watched = s.memory watched)
      0 (witnessBranchAt 4) := by
  have first : Reaches s (witnessBranchAt 2)
      (fun next => next.locals = s.locals ∧ next.globals = s.globals ∧ next.code = s.code ∧
        next.memaddrs = s.memaddrs ∧ next.be = s.be ∧
        ∀ watched : BitVec 64, watched ≠ branch+32+index*8 → next.memory watched = s.memory watched)
      0 (witnessBranchAt 3) := by
    rw [source_witness_branch_child_store_sequence]
    apply runBounded_seq_reaches s witnessBranchChildStore (witnessBranchAt 3) _ 0
      (RunBounded.ofProg (ProgBounded.straight _ (by rw [source_witness_branch_child_store_fragment]; rfl)) code (by omega))
    · intro value
      exact evaluate_noDirectReturn _ (by rw [source_witness_branch_child_store_fragment]; rfl) s value
    · intro next normal
      have control := evaluate_store_control_frame s
        (.op .add [.var .local (ofString "br"),.const 32,.panop .mul [.var .local (ofString "i"),.const 8]])
        (.var .local (ofString "result"))
      have localControl := control.2.1
      rw [← source_witness_branch_child_store_fragment] at localControl
      have globals := prefix_globals witnessBranchChildStore (by intro watched; rw [source_witness_branch_child_store_fragment]; rfl) s code
      have metadata := evaluateHOLFiniteState_metadata s witnessBranchChildStore
      rw [normal] at localControl globals metadata
      refine ⟨localControl,globals,metadata.1,metadata.2.1,metadata.2.2.1,?_⟩
      intro watched separate
      have frame := witness_branch_child_store_word_frame s branch index result watched atBr atIndex atResult separate
      rw [normal] at frame
      exact frame
  apply reaches_trans s (witnessBranchAt 2) (witnessBranchAt 3) (witnessBranchAt 4) _ _ 0 0 first
  intro ready facts
  obtain ⟨locals,globals,codeEq,domain,endian,memory⟩ := facts
  rw [source_witness_branch_occupancy_sequence]
  apply runBounded_seq_reaches ready witnessBranchOccupancyUpdate (witnessBranchAt 4) _ 0
    (RunBounded.ofProg (ProgBounded.straight _ (by rw [source_witness_branch_occupancy_fragment]; rfl)) (codeEq.trans code) (by omega))
  · intro value
    exact evaluate_noDirectReturn _ (by rw [source_witness_branch_occupancy_fragment]; rfl) ready value
  · intro next normal
    have localsNext := occupancy_locals ready
    have globalsNext := prefix_globals witnessBranchOccupancyUpdate
      (by intro watched; rw [source_witness_branch_occupancy_fragment]; rfl) ready (codeEq.trans code)
    have metadata := evaluateHOLFiniteState_metadata ready witnessBranchOccupancyUpdate
    rw [normal] at localsNext globalsNext metadata
    refine ⟨localsNext.trans locals,globalsNext.trans globals,metadata.1.trans codeEq,
      metadata.2.1.trans domain,metadata.2.2.1.trans endian,?_⟩
    intro watched firstSeparate secondSeparate
    have frame := witness_branch_occupancy_word_frame ready top watched (by rw [locals]; exact atTop) secondSeparate
    rw [normal] at frame
    exact frame.trans (memory watched firstSeparate)

theorem witness_branch_prelude_normal_continuation {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top branch index result : BitVec 64)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (atBr : s.locals.lookup (ofString "br") = some (.val (.word branch)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (witnessBranchAt 2) = (none,post)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      ready.locals = s.locals ∧ ready.globals = s.globals ∧ ready.code = s.code ∧
      ready.memaddrs = s.memaddrs ∧ ready.be = s.be ∧
      evaluateHOLFiniteState ready (witnessBranchAt 4) = (none,post) ∧
      ∀ watched : BitVec 64, watched ≠ branch+32+index*8 → watched ≠ top+40 →
        ready.memory watched = s.memory watched := by
  rw [source_witness_branch_child_store_sequence] at run
  obtain ⟨stored,firstRun,rest⟩ := witness_extension_sequence_normal_parts s post _ _ run
  rw [source_witness_branch_occupancy_sequence] at rest
  obtain ⟨ready,occRun,tailRun⟩ := witness_extension_sequence_normal_parts stored post _ _ rest
  have firstLocals := (evaluate_store_control_frame s
    (.op .add [.var .local (ofString "br"),.const 32,.panop .mul [.var .local (ofString "i"),.const 8]])
    (.var .local (ofString "result"))).2.1
  rw [← source_witness_branch_child_store_fragment,firstRun] at firstLocals
  have nextLocals := occupancy_locals stored
  rw [occRun] at nextLocals
  have firstGlobals := prefix_globals witnessBranchChildStore
    (by intro watched; rw [source_witness_branch_child_store_fragment]; rfl) s code
  have firstMetadata := evaluateHOLFiniteState_metadata s witnessBranchChildStore
  rw [firstRun] at firstGlobals firstMetadata
  have nextGlobals := prefix_globals witnessBranchOccupancyUpdate
    (by intro watched; rw [source_witness_branch_occupancy_fragment]; rfl) stored (firstMetadata.1.trans code)
  have nextMetadata := evaluateHOLFiniteState_metadata stored witnessBranchOccupancyUpdate
  rw [occRun] at nextGlobals nextMetadata
  refine ⟨ready,nextLocals.trans firstLocals,nextGlobals.trans firstGlobals,nextMetadata.1.trans firstMetadata.1,
    nextMetadata.2.1.trans firstMetadata.2.1,nextMetadata.2.2.1.trans firstMetadata.2.2.1,tailRun,?_⟩
  intro watched firstSeparate secondSeparate
  have one := witness_branch_child_store_word_frame s branch index result watched atBr atIndex atResult firstSeparate
  have two := witness_branch_occupancy_word_frame stored top watched (by rw [firstLocals]; exact atTop) secondSeparate
  rw [firstRun] at one
  rw [occRun] at two
  exact two.trans one

#print axioms witness_branch_prelude_reaches
#print axioms witness_branch_prelude_normal_continuation
end InitECandidate.Runtime
