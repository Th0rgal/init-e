import InitECandidate.Runtime.PtBalKeep2GD
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete whole-program check for every original body in the additional
BAL call closure, simultaneously checking all five watched globals. -/
theorem program_check_bal_globals2 : (functionsHOL sourceDeclarations).all
 (fun entry=> !(balExtra2.contains entry.1) || balWatched.all
  (fun watched=>keepsG watched goodBal2 entry.2.2.1))=true := by
 decide_cbv

/-- Discharge the named BAL preservation obligation using installed code. -/
theorem bal_keep2_checked : BalKeep2 := by
 intro watched member function extra params body shape installed
 have checked:=List.all_eq_true.mp program_check_bal_globals2 _ (originalRuntimeCode_mem installed)
 simp only [extra,Bool.not_true,Bool.false_or] at checked
 exact List.all_eq_true.mp checked watched member

#print axioms program_check_bal_globals2
#print axioms bal_keep2_checked
end InitECandidate.Runtime
