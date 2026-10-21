import InitECandidate.Runtime.GuestCostEntryStatic
import InitECandidate.Runtime.GuestCostSharpSites
import InitECandidate.Runtime.GuestCostGlobalsInit
import InitECandidate.Runtime.GuestCostGlobalsReady
import InitECandidate.Runtime.GuestCostSyntax
import InitECandidate.Runtime.OriginalDeclarationReorder
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open InitE InitECandidate.Proofs.FrontendStages

/-! The end-to-end transfer for the guest: the original `main` run from the
post-declaration state of the authoritative source program. -/

theorem guest_mem_functions {ds : List (DeclHOL 64)} {entry : MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (h : entry ∈ functionsHOL ds) :
    ∃ f : FunDeclHOL 64, DeclHOL.function f ∈ ds ∧ entry = (f.name, f.params, f.body, f.returnShape) := by
  induction ds with
  | nil => simp [functionsHOL] at h
  | cons d ds ih =>
    cases d with
    | function f =>
      simp only [functionsHOL, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨f, by simp, rfl⟩
      · obtain ⟨g, hg, rfl⟩ := ih h; exact ⟨g, by simp [hg], rfl⟩
    | decl _ _ _ => simp only [functionsHOL] at h; obtain ⟨g, hg, rfl⟩ := ih h; exact ⟨g, by simp [hg], rfl⟩
    | exnDecl _ _ => simp only [functionsHOL] at h; obtain ⟨g, hg, rfl⟩ := ih h; exact ⟨g, by simp [hg], rfl⟩
    | name _ _ => simp only [functionsHOL] at h; obtain ⟨g, hg, rfl⟩ := ih h; exact ⟨g, by simp [hg], rfl⟩

theorem guest_simplified_eq_pass1 : panSimpDeclsHOL InitE.sourceDeclarations = pass1 := pass0_eq

theorem guest_entry_program :
    compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) (Flapjack.Basis.Pure.MlString.ofString "main") =
      pass2 := by
  rw [guest_simplified_eq_pass1]; exact pass2_eq

theorem guest_pass2_no_inline_local :
    (functionsHOL (pass2.filter inlinableHOL)).map Prod.fst = [] := by
  decide_cbv

theorem guest_source_distinct : ((functionsHOL InitE.sourceDeclarations).map Prod.fst).Nodup := by
  decide_cbv

theorem guest_source_eids : sizeOfEidsHOL InitE.sourceDeclarations < 2 ^ 64 := by
  decide_cbv

theorem guest_source_aligned (input : Guest.InputBlob) :
    panGlobalsByteAlignedHOL (sourceInitialState input).topAddr := by
  simp only [sourceInitialState]; unfold panGlobalsByteAlignedHOL; decide_cbv

/-- The guest's globals area size, as in the pinned `pan_to_word` premises. -/
noncomputable def guestGlobalsSize : Nat :=
  ((decShapesHOL InitE.sourceDeclarations).map
    (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact (width := 64) [] InitE.sourceDeclarations)))).sum

#print axioms guest_pass2_no_inline_local
#print axioms guest_source_aligned
end InitECandidate.Runtime.FineCost
