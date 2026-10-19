import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

theorem witness_iteration_db_avoids : avoidsLocal (ofString "db") decodeWitnessNodeIteration=true := by
  decide_cbv

theorem witness_iteration_db_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeIteration=(none,post)) :
    post.locals.lookup (ofString "db")=s.locals.lookup (ofString "db") := by
  have kept := evaluate_avoidsLocal_flowing (ofString "db") decodeWitnessNodeIteration witness_iteration_db_avoids s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms witness_iteration_db_avoids
#print axioms witness_iteration_db_normal_kept

theorem witness_decode_go_avoids : avoidsLocal (ofString "go") decodeWitnessNodeDecodeMode=true := by
  decide_cbv

theorem witness_decode_go_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) :
    post.locals.lookup (ofString "go")=s.locals.lookup (ofString "go") := by
  have kept := evaluate_avoidsLocal_flowing (ofString "go") decodeWitnessNodeDecodeMode witness_decode_go_avoids s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms witness_decode_go_avoids
#print axioms witness_decode_go_normal_kept

theorem witness_resolve_go_avoids : avoidsLocal (ofString "go") decodeWitnessNodeResolveMode=true := by
  decide_cbv

theorem witness_resolve_go_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    post.locals.lookup (ofString "go")=s.locals.lookup (ofString "go") := by
  have kept := evaluate_avoidsLocal_flowing (ofString "go") decodeWitnessNodeResolveMode witness_resolve_go_avoids s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms witness_resolve_go_avoids
#print axioms witness_resolve_go_normal_kept

theorem witness_unwind_nonempty_go_avoids : avoidsLocal (ofString "go") witnessUnwindNonempty=true := by
  decide_cbv

theorem witness_unwind_nonempty_go_normal_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s witnessUnwindNonempty=(none,post)) :
    post.locals.lookup (ofString "go")=s.locals.lookup (ofString "go") := by
  have kept := evaluate_avoidsLocal_flowing (ofString "go") witnessUnwindNonempty witness_unwind_nonempty_go_avoids s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
#print axioms witness_unwind_nonempty_go_avoids
#print axioms witness_unwind_nonempty_go_normal_kept
end InitECandidate.Runtime
