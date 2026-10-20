import InitECandidate.Runtime.SourceCostGlobalsReady
import InitECandidate.Proofs.FrontendStages.Pass1
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang
open InitECandidate.Proofs.FrontendStages

/-- Syntactic requirements for the actual input of `pan_globals`, including
the generated temporary's freshness in function parameters. -/
def globalsReadyDecl : DeclHOL 64 → Bool
  | .function function => globalsReadyProg function.body &&
      decide (globalsTemp ∉ function.params.map Prod.fst)
  | .decl _ _ value => globalsReadyExp value
  | _ => true

/-- Check all original installed functions and initializers at the exact
post-structs/pre-globals compiler stage. This is not a runtime bound. -/
theorem guest_globals_ready : pass1.all globalsReadyDecl = true := by
  decide_cbv

theorem guest_globals_body_ready (function : FunDeclHOL 64)
    (member : DeclHOL.function function ∈ pass1) :
    globalsReadyProg function.body = true ∧ globalsTemp ∉ function.params.map Prod.fst := by
  have ready := List.all_eq_true.mp guest_globals_ready _ member
  simpa only [globalsReadyDecl, Bool.and_eq_true, decide_eq_true_eq] using ready

#print axioms guest_globals_ready
#print axioms guest_globals_body_ready
end InitECandidate.Runtime.FineCost
