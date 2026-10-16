import InitECandidate.Runtime.BaselineGlobalsLayout
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- Original source runtime before global declarations, after exception setup. -/
noncomputable def canonicalGlobalsSourceState (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {sourceInitialState input with eshapes := (canonicalPanEntryState input).eshapes}

/-- The installed frontend memory satisfies the original global-lowering
initial relation, including actual backing memory and reserved globals tail. -/
theorem canonical_globals_initial_relation (input : Guest.InputBlob) :
    panGlobalsStateRelHOLExact false FrontendStages.Declarations.globalInitial
      (canonicalGlobalsSourceState input) (canonicalPanEntryState input) := by
  classical
  unfold panGlobalsStateRelHOLExact
  refine ⟨?_,?_,?_,?_,rfl,?_,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,Or.inr rfl⟩
  · change (sourceInitialState input).topAddr =
      (canonicalPanDeclarationState input).topAddr -
        FrontendStages.Declarations.globalInitial.maxGlobalsSize
    rw [canonical_pan_source_top]
    change _ = _ + panBytesInWord 64 * BitVec.ofNat 64 globalsWords -
      cakeBytesInWord 64 * BitVec.ofNat 64 93
    have bytes : cakeBytesInWord 64 = panBytesInWord 64 := by decide_cbv
    rw [bytes]
    change _ = _ + panBytesInWord 64 * 93#64 - panBytesInWord 64 * 93#64
    rw [BitVec.add_sub_cancel]
  · intro impossible; cases impossible
  · exact (canonical_pan_declaration_base input).symm
  · exact (canonical_pan_endian input).symm
  · exact (canonical_pan_declaration_clock input).symm
  · intro name value lookup; cases lookup
  · intro name shape address lookup; cases lookup
  · intro address valid
    change (canonicalPanDeclarationState input).memaddrs address
    rw [canonical_pan_source_domain]
    exact Or.inl valid
  · exact (canonical_pan_shared_domain input).symm
  · intro address valid
    exact (canonical_pan_memory_agreement input address valid).symm
  · exact (canonical_pan_declaration_ffi input).symm
  · intro name params body shape lookup; cases lookup
  · intro name1 name2 shape1 address1 shape2 address2 different present
    exact (present rfl).elim
  · exact canonical_pan_top_outside input
  · change panGlobalsByteAlignedHOL (canonicalPanDeclarationState input).topAddr
    rw [canonical_pan_heap_top]
    exact baseline_globals_top_aligned

#print axioms canonical_globals_initial_relation
end InitECandidate.Runtime
