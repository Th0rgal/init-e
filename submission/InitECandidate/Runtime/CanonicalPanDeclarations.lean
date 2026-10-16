import InitECandidate.Runtime.CanonicalPanNative
import InitECandidate.Runtime.BaselinePanDeclarationSetup
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Global-lowered declaration state before the original evaluator installs
functions and exception shapes. Runtime fields are the canonical initialized ones. -/
noncomputable def canonicalPanDeclarationState (input : Guest.InputBlob) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {canonicalPanEntryState input with code := HolFiniteMapExact.empty, eshapes := HolFiniteMapExact.empty}

theorem canonical_pan_declarations_evaluate (input : Guest.InputBlob) (fuel : Nat)
    [DecidablePred (canonicalPanDeclarationState input).memaddrs] :
    evaluateDeclsHOLFinite {canonicalPanDeclarationState input with clock := fuel} FrontendStages.pass2 =
      some {canonicalPanEntryState input with clock := fuel} := by
  have initialized := panDeclarationSetup_evaluates FrontendStages.pass2
    {canonicalPanDeclarationState input with clock := fuel} baseline_pan_declaration_setup
  change evaluateDeclsHOLFinite {canonicalPanDeclarationState input with clock := fuel} FrontendStages.pass2 =
    some {{canonicalPanDeclarationState input with clock := fuel} with
      code := HolFiniteMapExact.empty.updateList (functionsHOL FrontendStages.pass2)
      eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.pass2)} at initialized
  rw [function_table_reverse _ baseline_pan_distinct] at initialized
  exact initialized

#print axioms canonical_pan_declarations_evaluate
end InitECandidate.Runtime
