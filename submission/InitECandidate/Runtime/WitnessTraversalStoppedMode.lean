import InitECandidate.Runtime.WitnessTraversalIterationClosure
import InitECandidate.Runtime.WitnessModeCallerLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The sole actual go=0 update is the empty-stack delivery in mode zero. -/
theorem WitnessTraversalState.iteration_stopped_mode {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
 (valid : WitnessTraversalState layout s scratch heap top mode go) (running : go=1)
 (run : evaluateHOLFiniteState s decodeWitnessNodeIteration=(none,post))
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64)))) :
 post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) := by
 have atGo : s.locals.lookup (ofString "go")=some (.val (.word (1#64))) := by rw [valid.atGo,running];rfl
 rcases valid.modes with unwind | decode | resolve
 · have modeLocal:=valid.atMode
   rw [unwind] at modeLocal
   have modeRun:=(witness_iteration_dispatch_unwind s modeLocal).symm.trans run
   by_cases empty : top=0
   · subst top
     have postEq:=witness_unwind_empty_normal_progress s post valid.atTop modeRun
     rw [postEq]
     simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using modeLocal
   · have kept:=(witness_unwind_nonempty_mode_go_normal_kept s post top valid.atTop empty modeRun).trans atGo
     rw [stopped] at kept
     cases kept
 · have modeLocal:=valid.atMode
   rw [decode] at modeLocal
   have modeRun:=(witness_iteration_dispatch_decode s modeLocal).symm.trans run
   have kept:=(witness_decode_go_normal_kept s post modeRun).trans atGo
   rw [stopped] at kept
   cases kept
 · have modeLocal:=valid.atMode
   rw [resolve] at modeLocal
   have modeRun:=(witness_iteration_dispatch_resolve s modeLocal).symm.trans run
   have kept:=(witness_resolve_go_normal_kept s post modeRun).trans atGo
   rw [stopped] at kept
   cases kept
#print axioms WitnessTraversalState.iteration_stopped_mode
end InitECandidate.Runtime
