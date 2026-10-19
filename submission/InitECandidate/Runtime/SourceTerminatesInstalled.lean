import InitECandidate.Runtime.Bounds
import InitECandidate.Runtime.OriginalDeclarationReorder
import InitE.SourceShapeFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A source-fuel witness transports to any actual initialized main-first
declaration state. Reordering preserves both initialization and the fuel. -/
theorem sourceTerminatesAt_installed (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (fuel : Nat)
    (entry : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installation : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ (sourceInitialState input)
      (fun address => Classical.propDecidable ((sourceInitialState input).memaddrs address))
      sourceDeclarations = some entry)
    (source : sourceTerminatesAt input outcome events fuel) :
    ∃ result post,
      evaluateHOLFiniteState {entry with clock := fuel}
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
  have installedEq : installed = entry := Option.some.inj (normalizedRun.symm.trans installation)
  subst installed
  exact ⟨result, post, run, terminal, trace⟩
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.sourceTerminatesAt_installed
