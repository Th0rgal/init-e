import InitECandidate.Runtime.CanonicalSourceDeclarations
import InitECandidate.Runtime.PanSimpDeclarationReflection
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The actual simplifier output initializes successfully on original memory. -/
theorem canonical_simplified_declarations_evaluate (input : Guest.InputBlob) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ {sourceInitialState input with code := HolFiniteMapExact.empty}
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      (panSimpDeclsHOL sourceDeclarations) = some (canonicalUnrenamedSourceEntry input) := by
  rw [FrontendStages.pass0_eq]
  exact canonical_source_declarations_evaluate input

/-- Original challenge declarations initialize, and the full simplifier state
relation identifies their result with the quantitative runtime entry. -/
theorem canonical_original_source_entry_exists (input : Guest.InputBlob) :
    ∃ original, @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      sourceDeclarations = some original ∧
      PanSimp.stateRel original (canonicalUnrenamedSourceEntry input)
        (canonicalUnrenamedSourceEntry input).code := by
  classical
  obtain ⟨original,sourceRun⟩ := pan_simp_declarations_reflect sourceDeclarations (sourceInitialState input)
    (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
    HolFiniteMapExact.empty (canonicalUnrenamedSourceEntry input) (canonical_simplified_declarations_evaluate input)
  have codeRel : PanSimp.CodeRel (sourceInitialState input).code HolFiniteMapExact.empty := by
    refine ⟨fun _ _ => rfl,?_⟩
    intro name params body shape impossible
    cases impossible
  obtain ⟨code,simplifiedRun,related⟩ := PanSimp.evaluateDeclsCodeRel sourceDeclarations
    (sourceInitialState input) _ HolFiniteMapExact.empty original codeRel sourceRun
  have equal : canonicalUnrenamedSourceEntry input = {original with code := code} :=
    Option.some.inj ((canonical_simplified_declarations_evaluate input).symm.trans simplifiedRun)
  have codeEq : (canonicalUnrenamedSourceEntry input).code = code :=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) equal
  refine ⟨original,sourceRun,?_⟩
  rw [codeEq]
  exact ⟨equal,related.1,related.2⟩

noncomputable def canonicalOriginalSourceEntry (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory := Classical.choose (canonical_original_source_entry_exists input)

theorem canonical_original_declarations_evaluate (input : Guest.InputBlob) :
    @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      sourceDeclarations = some (canonicalOriginalSourceEntry input) :=
  (Classical.choose_spec (canonical_original_source_entry_exists input)).1

theorem canonical_original_simplified_relation (input : Guest.InputBlob) :
    PanSimp.stateRel (canonicalOriginalSourceEntry input) (canonicalUnrenamedSourceEntry input)
      (canonicalUnrenamedSourceEntry input).code :=
  (Classical.choose_spec (canonical_original_source_entry_exists input)).2

#print axioms canonical_original_source_entry_exists
#print axioms canonical_original_declarations_evaluate
#print axioms canonical_original_simplified_relation
end InitECandidate.Runtime
