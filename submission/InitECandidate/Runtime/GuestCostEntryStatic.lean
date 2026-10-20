import InitECandidate.Runtime.SourceCostInitial
import InitECandidate.Proofs.FrontendStages.Pass0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang
open InitECandidate.Proofs.FrontendStages

theorem guest_source_kinds :
    InitE.sourceDeclarations.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true := by
  decide_cbv

/-- The source declarations need no structure context. -/
theorem guest_source_struct_context :
    decsStcnamesHOLExact (width := 64) [] InitE.sourceDeclarations = some [] :=
  decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls [] _ guest_source_kinds

theorem guest_main_shape :
    (List.lookup (Flapjack.Basis.Pure.MlString.ofString "main") (functionsHOL pass0)).map
      (fun entry => (entry.1.isEmpty, sizeOfShapeHOL entry.2.2)) = some (true, 1) := by
  decide_cbv

/-- `main` of the simplified program takes no parameters and returns one word. -/
theorem guest_main_lookup : ∃ body rshape,
    List.lookup (Flapjack.Basis.Pure.MlString.ofString "main")
      (functionsHOL (panSimpDeclsHOL InitE.sourceDeclarations)) = some ([], body, rshape) ∧
    sizeOfShapeHOL rshape = 1 := by
  rw [pass0_eq]
  have h := guest_main_shape
  rcases hl : List.lookup (Flapjack.Basis.Pure.MlString.ofString "main") (functionsHOL pass0) with
    _ | ⟨params, body, rshape⟩
  · rw [hl] at h; cases h
  · rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨body, rshape, rfl, hs⟩

#print axioms guest_source_struct_context
#print axioms guest_main_lookup
end InitECandidate.Runtime.FineCost
