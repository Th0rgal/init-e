import InitECandidate.Runtime.BaselineCompiledFunctions
import InitECandidate.Runtime.BaselineGlobalEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

noncomputable def baselineGlobalWrapperEntry :
    MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  (baselineCrepStart,[],.seq (nestedSeqHOL FrontendStages.Declarations.globalInitializers)
    (.call none FrontendStages.Declarations.globalNewStart []),.one)

/-- The concrete function table consists of the generated wrapper followed by
exactly the compiled renamed source table. -/
theorem baseline_global_function_table :
    functionsHOL FrontendStages.pass2 = baselineGlobalWrapperEntry ::
      compileFunctionEntries FrontendStages.Declarations.globalContext
        (functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) := by
  calc
    _ = baselineGlobalWrapperEntry :: functionsHOL FrontendStages.Declarations.translatedFunctions := by kernel_rfl
    _ = _ := by rw [baseline_compiled_functions]

private theorem lookup_member_distinct {A B : Type} [BEq A] [LawfulBEq A]
    (entries : List (A × B)) (name : A) (value : B)
    (member : (name,value) ∈ entries) (distinct : (entries.map Prod.fst).Nodup) :
    List.lookup name entries = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries ih =>
    obtain ⟨key,entryValue⟩ := entry
    simp only [List.map_cons,List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with equal | member
    · cases equal; simp
    · have different : name ≠ key := by
        intro equal
        have present : name ∈ entries.map Prod.fst := List.mem_map.mpr ⟨(name,value),member,rfl⟩
        exact distinct.1 (equal ▸ present)
      simp only [List.lookup_cons,show (name == key) = false by simp [different]]
      exact ih member distinct.2

/-- Every source function has its compiled body installed in the actual
canonical entry code; the wrapper cannot shadow any compiled source entry. -/
theorem canonical_compiled_function_lookup (input : Guest.InputBlob)
    (name : MlS) (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (member : (name,params,body,shape) ∈
      functionsHOL FrontendStages.Declarations.renamedFunctionDeclarations) :
    (canonicalPanEntryState input).code.lookup name =
      some (params,compileProgExactHOL FrontendStages.Declarations.globalContext body,shape) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL FrontendStages.pass2).reverse).lookup name = _
  calc
    _ = List.lookup name (functionsHOL FrontendStages.pass2) := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup _ _
    _ = _ := by
      apply lookup_member_distinct _ _ _ _ baseline_pan_distinct
      rw [baseline_global_function_table]
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨(name,params,body,shape),member,rfl⟩


#print axioms baseline_global_function_table
#print axioms canonical_compiled_function_lookup
end InitECandidate.Runtime
