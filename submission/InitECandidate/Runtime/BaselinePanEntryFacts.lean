import InitECandidate.Runtime.PanCrepEntryClock
import Flapjack.Pancake.Proofs.PanGlobals.CompileLocalised
import InitECandidate.Proofs.FrontendStages.Pass3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang InitECandidate.Proofs

theorem baseline_pan_distinct : ((functionsHOL FrontendStages.pass2).map Prod.fst).Nodup := by
  apply of_decide_eq_true
  kernel_rfl

theorem baseline_pan_localised :
    ∀ entry ∈ functionsHOL FrontendStages.pass2, localisedProgHOL entry.2.2.1 = true := by
  rw [← FrontendStages.pass2_eq]
  exact compileTopLocalisedHOL _ _

theorem baseline_pan_eids_size : sizeOfEidsHOL FrontendStages.pass2 < 2 ^ 64 := by
  apply of_decide_eq_true
  kernel_rfl

#print axioms baseline_pan_distinct
#print axioms baseline_pan_localised
#print axioms baseline_pan_eids_size
end InitECandidate.Runtime
