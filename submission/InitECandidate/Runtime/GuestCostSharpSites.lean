import InitECandidate.Runtime.SourceCostSharpCrepBasis
import InitECandidate.Proofs.FrontendStages.Pass2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang
open InitECandidate.Proofs.FrontendStages

/-- Every expression and body of a declaration satisfies the site certificate. -/
def guestSharpSitesDecl (bound : Nat) : DeclHOL 64 → Bool
  | .function function => sharpSitesProg bound function.body
  | .decl _ _ value => sharpSites bound value
  | _ => true

/-- The exact program `pan_to_crep` compiles (after `pan_simp`, `pan_structs`
and `pan_globals`, with the generated entry) meets the replay certificate at
the fixed bound. -/
theorem guest_pass2_sharp_sites : pass2.all (guestSharpSitesDecl sharpReplayBound) = true := by
  decide_cbv

/-- The simplified source program meets it too. -/
theorem guest_pass0_sharp_sites : pass0.all (guestSharpSitesDecl sharpReplayBound) = true := by
  decide_cbv

#print axioms guest_pass2_sharp_sites
#print axioms guest_pass0_sharp_sites
end InitECandidate.Runtime.FineCost
