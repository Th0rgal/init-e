import InitECandidate.Runtime.SourceCostSharpCrepBasis
import InitECandidate.Runtime.SourceCostPanStructsId
import InitECandidate.Runtime.SourceCostCrepInlineId
import InitECandidate.Proofs.FrontendStages.Pass0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-- Inspect all expressions and bodies, not just reached dynamic paths. -/
def sharpSitesDecl (bound : Nat) : DeclHOL 64 → Bool
  | .function function => sharpSitesProg bound function.body
  | .decl _ _ value => sharpSites bound value
  | _ => true

/-- The actual simplified declarations contain no named structures, hence the
pinned structures pass is the identity on this exact compiler stage. -/
theorem guest_simplified_struct_free :
    structFreeDecls (panSimpDeclsHOL InitE.sourceDeclarations) = true := by
  rw [InitECandidate.Proofs.FrontendStages.pass0_eq]
  decide_cbv

/-- The actual simplified program has no functions marked for inlining. -/
theorem guest_simplified_no_inline :
    (functionsHOL ((panSimpDeclsHOL InitE.sourceDeclarations).filter inlinableHOL)).map Prod.fst = [] := by
  rw [InitECandidate.Proofs.FrontendStages.pass0_eq]
  decide_cbv

#print axioms guest_simplified_struct_free
#print axioms guest_simplified_no_inline
end InitECandidate.Runtime.FineCost
