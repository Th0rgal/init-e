import InitECandidate.Runtime.Bounds
import InitECandidate.Runtime.CanonicalOriginalSourceEntry
import InitE.SourceShapeFacts
import InitECandidate.Runtime.OriginalDeclarationReorder
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- The abstract source-fuel witness is execution of the canonical original
installed declarations, with exactly its original fuel and observation. -/
theorem sourceTerminatesAt_canonical_entry (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (fuel : Nat)
    (source : sourceTerminatesAt input outcome events fuel) :
    ∃ result post,
      evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock := fuel}
        (.call none (Flapjack.Basis.Pure.MlString.ofString "main") []) = (some result, post) ∧
      (match result with
        | .finalFfi ffi => outcome = HolOutcome.ffiOutcome ffi
        | .returned _ => outcome = .success
        | _ => False) ∧ post.ffi.ioEvents = events := by
  classical
  obtain ⟨context, installed, result, post, contextRun, installedRun, run, terminal, trace⟩ := source
  have normalizedContext : decsStcnamesHOLExact [] sourceDeclarations = some context :=
    original_declaration_context.trans contextRun
  have contextEq : context = [] := Option.some.inj (normalizedContext.symm.trans sourceStructContext)
  subst context
  have initialEq : {sourceInitialState input with structs := []} = sourceInitialState input := rfl
  rw [initialEq] at installedRun
  have normalizedRun : evaluateDeclsHOLFinite (sourceInitialState input) sourceDeclarations = some installed :=
    (original_declaration_evaluation (sourceInitialState input)).trans installedRun
  have installedEq : installed = canonicalOriginalSourceEntry input :=
    Option.some.inj (normalizedRun.symm.trans (canonical_original_declarations_evaluate input))
  subst installed
  exact ⟨result, post, run, terminal, trace⟩
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.sourceTerminatesAt_canonical_entry
