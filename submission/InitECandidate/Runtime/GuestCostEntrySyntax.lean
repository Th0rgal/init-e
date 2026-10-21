import InitECandidate.Runtime.GuestCostSharpSites
import InitECandidate.Runtime.SourceCostCrepInlineId
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang
open InitECandidate.Proofs.FrontendStages

/-- Globals lowering, including the generated entry, introduces no marked
inlining functions in the exact program supplied to pan_to_crep. -/
theorem guest_pass2_no_inline :
    (functionsHOL (pass2.filter inlinableHOL)).map Prod.fst = [] := by
  decide_cbv

def localisedDecl : DeclHOL 64 → Bool
  | .function function => localisedProgHOL function.body
  | .decl _ _ value => localisedExpHOL value
  | _ => true

/-- Every installed function and initializer in the actual post-globals stage
uses localized variables, including the generated entry body. -/
theorem guest_pass2_localised : pass2.all localisedDecl = true := by
  decide_cbv

theorem guest_pass2_body_localised (function : FunDeclHOL 64)
    (member : DeclHOL.function function ∈ pass2) : localisedProgHOL function.body = true :=
  List.all_eq_true.mp guest_pass2_localised _ member

#print axioms guest_pass2_no_inline
#print axioms guest_pass2_localised
#print axioms guest_pass2_body_localised
end InitECandidate.Runtime.FineCost
