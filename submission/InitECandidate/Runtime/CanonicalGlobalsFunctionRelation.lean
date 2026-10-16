import InitECandidate.Runtime.BaselineGlobalFunctionTable
import InitECandidate.Runtime.PanGlobalsCodeRelation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Initialization preserves the actual installed function table. -/
theorem canonical_globals_ready_code (input : Guest.InputBlob) :
    (canonicalInitializedGlobals input).code = (canonicalPanEntryState input).code := by
  have invariant := evaluateInvariantsHOLFinite
    (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (canonicalPanEntryState input)) none
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (canonicalInitializedGlobals input)) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,canonical_globals_ready_run])
  exact invariant.2.2.2.2.2.2.1

noncomputable def canonicalRenamedSourceEntry (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {zeroGlobalPost (canonicalGlobalsSourceState input) baselineGlobalNames with
    locals := (canonicalInitializedGlobals input).locals
    code := HolFiniteMapExact.empty.updateList
      (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations).reverse}

private theorem lookup_member {A B : Type} [BEq A] [LawfulBEq A]
    (entries : List (A × B)) (name : A) (value : B)
    (lookup : List.lookup name entries = some value) : (name,value) ∈ entries := by
  induction entries with
  | nil => simp at lookup
  | cons entry entries ih =>
    obtain ⟨key,entryValue⟩ := entry
    by_cases equal : name = key
    · subst equal; simp at lookup; subst lookup; simp
    · simp only [List.lookup_cons,show (name == key) = false by simp [equal]] at lookup
      exact List.mem_cons_of_mem _ (ih lookup)

/-- Full source/target simulation relation after global initialization and
installation of the renamed source functions, at any shared runtime clock. -/
theorem canonical_globals_function_relation (input : Guest.InputBlob) (fuel : Nat) :
    panGlobalsStateRelHOLExact true FrontendStages.Declarations.globalContext
      {canonicalRenamedSourceEntry input with clock := fuel}
      {canonicalInitializedGlobals input with clock := fuel} := by
  apply pan_globals_relation_clock
  apply pan_globals_install_code _ _ _ _ (canonical_globals_ready_relation input)
  intro name params body shape lookup
  have sourceLookup : List.lookup name
      (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) = some (params,body,shape) := by
    exact (FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _).symm.trans lookup
  rw [canonical_globals_ready_code]
  exact canonical_compiled_function_lookup input name params body shape (lookup_member _ _ _ sourceLookup)

#print axioms canonical_globals_ready_code
#print axioms canonical_globals_function_relation
end InitECandidate.Runtime
