import InitECandidate.Runtime.BaselineCrepSimplified
namespace InitECandidate.Runtime
open Flapjack InitECandidate.Proofs

/-- The source state actually used by the original Crep-to-Loop entry proof
satisfies the fixed procedure ceiling after arithmetic simplification. -/
theorem baseline_crep_entry_state_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (memory : BitVec 64 → HolWordLab 64) :
    CrepCodeSize baselineCrepLimit
      (crepSimpMapcsHOL (crepStateHOL s FrontendStages.pass2 memory)) := by
  apply baseline_simplified_crep_bounded
  change HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW FrontendStages.pass2).reverse = _
  rw [FrontendStages.pass3_eq]

#print axioms baseline_crep_entry_state_bounded
end InitECandidate.Runtime
