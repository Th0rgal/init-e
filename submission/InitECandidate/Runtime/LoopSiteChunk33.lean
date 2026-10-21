import InitECandidate.Runtime.LoopWordPLCallTab
import InitECandidate.Proofs.FrontendStages.Loop.Data825
namespace InitECandidate.Runtime.FineCost
open Flapjack

theorem lsc_825 : (siteW siteA siteB (InitECandidate.Proofs.FrontendStages.Loop.output825.1, 2) InitECandidate.Proofs.FrontendStages.Loop.output825.2.2).isSome = true := by decide +kernel

def lsChunk33 : List (Nat × List Nat × HolLoopProg 64) := [InitECandidate.Proofs.FrontendStages.Loop.output825]

theorem lsChunk33_ok : ∀ x ∈ lsChunk33, (siteW siteA siteB (x.1, 2) x.2.2).isSome = true := by
  intro x hx
  simp only [lsChunk33, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx; exact lsc_825

#print axioms lsChunk33_ok
end InitECandidate.Runtime.FineCost
