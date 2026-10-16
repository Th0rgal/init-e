import InitECandidate.Runtime.CrepCodeList
import InitECandidate.Proofs.FrontendStages.Pass3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open Flapjack InitECandidate.Proofs

/-- Fixed conservative literal ceiling for the actual generated Crep table. -/
def baselineCrepLimit : Nat := 2 ^ 128

theorem baseline_crep_list_limit :
    crepCodeListLimit FrontendStages.pass3.reverse ≤ baselineCrepLimit := by
  apply of_decide_eq_true
  kernel_rfl

theorem baseline_crep_code_bounded {F : Type} (s : CrepSemHOLState 64 F)
    (installed : s.code = HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse) :
    CrepCodeSize baselineCrepLimit s := by
  have bounded := crep_code_list_bounded FrontendStages.pass3.reverse s installed
  intro name params body found
  exact Nat.le_trans (bounded name params body found) baseline_crep_list_limit

#print axioms baseline_crep_list_limit
#print axioms baseline_crep_code_bounded
end InitECandidate.Runtime
