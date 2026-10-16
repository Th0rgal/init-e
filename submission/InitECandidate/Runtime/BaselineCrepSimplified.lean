import InitECandidate.Runtime.CrepMapCodeList
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open Flapjack InitECandidate.Proofs

noncomputable def baselineSimplifiedCrepCode := FrontendStages.pass3.reverse.map
  (fun entry => (entry.1,entry.2.1,crepSimpProgHOL entry.2.2))

theorem baseline_simplified_crep_limit :
    crepCodeListLimit baselineSimplifiedCrepCode ≤ baselineCrepLimit := by
  apply of_decide_eq_true
  kernel_rfl

/-- The arithmetic simplification used by the actual entry proof installs
exactly the simplified generated list, with original finite-map behavior. -/
theorem baseline_simplified_crep_installed {F : Type} (s : CrepSemHOLState 64 F)
    (installed : s.code = HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse) :
    (crepSimpMapcsHOL s).code = HolFiniteMapExact.empty.updateList baselineSimplifiedCrepCode := by
  unfold crepSimpMapcsHOL
  dsimp only
  rw [installed,map2_updateList]
  rfl

theorem baseline_simplified_crep_bounded {F : Type} (s : CrepSemHOLState 64 F)
    (installed : s.code = HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse) :
    CrepCodeSize baselineCrepLimit (crepSimpMapcsHOL s) := by
  have bounded := crep_code_list_bounded baselineSimplifiedCrepCode (crepSimpMapcsHOL s)
    (baseline_simplified_crep_installed s installed)
  intro name params body found
  exact Nat.le_trans (bounded name params body found) baseline_simplified_crep_limit

#print axioms baseline_simplified_crep_limit
#print axioms baseline_simplified_crep_installed
#print axioms baseline_simplified_crep_bounded
end InitECandidate.Runtime
