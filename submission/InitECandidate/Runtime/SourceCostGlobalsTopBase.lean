import InitECandidate.Runtime.SourceCostGlobalsInit
import InitECandidate.Runtime.SourceCostFperm
import InitECandidate.Runtime.SourceCostDeclsClock
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every global laid out by `compile_decs` is set by `evaluate_decls`. -/
theorem globals_decls_cover {F : Type} :
    ∀ (decls : List (DeclHOL 64)) (context : PanGlobalsContextExact 64)
      (s s' : PanSemStateFiniteExact 64 F),
      @evaluateDeclsHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) decls = some s' →
      (∀ name entry, context.globals.lookup name = some entry → GlobalsPresent s name) →
      ∀ name entry, (compileDecsExactHOL context decls).2.2.2.globals.lookup name = some entry →
        GlobalsPresent s' name
  | [], context, s, s', h, cov => by
    simp only [evaluateDeclsHOLFinite, Option.some.injEq] at h
    subst h; simpa [compileDecsExactHOL] using cov
  | .name _ _ :: rest, context, s, s', h, cov => by
    simp only [evaluateDeclsHOLFinite] at h
    simp only [compileDecsExactHOL]
    exact globals_decls_cover rest context s s' h cov
  | .decl shape name expression :: rest, context, s, s', h, cov => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · split at h
      · rename_i value _ _
        simp only [compileDecsExactHOL]
        apply globals_decls_cover rest _ (setGlobalHOLFinite name value s) s' h
        intro n entry found
        simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
        unfold GlobalsPresent
        simp only [setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        split
        · simp
        · split at found
          · rename_i h1 h2; exact absurd (by simp_all) h1
          · exact cov n entry found
      · simp at h
    · simp at h
  | .function declaration :: rest, context, s, s', h, cov => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · simp only [compileDecsExactHOL]
      exact globals_decls_cover rest context _ s' h cov
    · simp at h
  | .exnDecl exceptionName shape :: rest, context, s, s', h, cov => by
    simp only [evaluateDeclsHOLFinite] at h
    split at h
    · simp only [compileDecsExactHOL]
      exact globals_decls_cover rest context _ s' h cov
    · simp at h

/-- Renaming functions keeps the `pan_globals` readiness certificate. -/
theorem globals_ready_fperm (f g : MlS) : ∀ p : ProgHOL 64,
    globalsReadyProg (fpermHOL f g p) = globalsReadyProg p
  | .dec name shape value body => by
    simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g body]
  | .seq a b => by simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g a, globals_ready_fperm f g b]
  | .ite e a b => by simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g a, globals_ready_fperm f g b]
  | .while e body => by simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g body]
  | .call info name args => by
    rcases info with _ | ⟨_ | ⟨kind, n⟩, _ | ⟨exception, handlerVar, handler⟩⟩
    all_goals (try cases kind)
    all_goals first
      | (simp only [fpermHOL, globalsReadyProg]; done)
      | simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g handler]
  | .decCall name shape function args body => by
    simp only [fpermHOL, globalsReadyProg, globals_ready_fperm f g body]
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .break | .continue | .raise _ _ | .return _
  | .tick | .extCall _ _ _ _ _ | .annot _ _ => by simp only [fpermHOL]
termination_by p => sizeOf p

#print axioms globals_decls_cover
#print axioms globals_ready_fperm
end InitECandidate.Runtime.FineCost
