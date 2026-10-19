import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
 theorem witness_unwind_db_avoids : avoidsLocal (ofString "db") decodeWitnessNodeUnwindMode=true := by
  decide_cbv
 theorem witness_unwind_db_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "db")=s.locals.lookup (ofString "db") := by
  have kept := evaluate_avoidsLocal_flowing (ofString "db") decodeWitnessNodeUnwindMode witness_unwind_db_avoids s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms witness_unwind_db_avoids
#print axioms witness_unwind_db_normal_kept
end InitECandidate.Runtime
