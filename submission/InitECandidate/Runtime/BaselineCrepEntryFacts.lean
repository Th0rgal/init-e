import InitECandidate.Runtime.BaselineCrepEntryState
import InitECandidate.Proofs.FrontendStages.Pass4
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open Flapjack InitECandidate.Proofs Flapjack.Basis.Pure.MlString

def baselineCrepStart : MlString := ofString "main"
noncomputable def baselineCrepMainBody : CrepProgHOL 64 :=
  (FrontendStages.pass3[0]'(by decide)).2.2

theorem baseline_crep_main : holAlookup FrontendStages.pass3 baselineCrepStart =
    some ([],baselineCrepMainBody) := by
  kernel_rfl

theorem baseline_crep_functions_main :
    (crepToLoopMakeFuncsExactHOL FrontendStages.pass3).lookup baselineCrepStart = some (firstLoopName,0) := by
  rw [← crepToLoopMakeFuncsExactExecutable_lookup_eq_HOL, FrontendStages.Loop.functionMap_eq]
  kernel_rfl

theorem baseline_crep_distinct : (FrontendStages.pass3.map Prod.fst).Nodup := by
  apply of_decide_eq_true
  kernel_rfl

theorem baseline_crep_call_size :
    sizeOf (CrepProgHOL.call none baselineCrepStart [] : CrepProgHOL 64) ≤ baselineCrepLimit := by
  apply of_decide_eq_true
  kernel_rfl

#print axioms baseline_crep_main
#print axioms baseline_crep_functions_main
#print axioms baseline_crep_distinct
#print axioms baseline_crep_call_size
end InitECandidate.Runtime
