import InitECandidate.Runtime.MptInsertNullStep
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def Stops (program : ProgHOL 64) : Prop :=
 ∀{F : Type}(s post : PanSemStateFiniteExact 64 F),
 evaluateHOLFiniteState s program=(none,post)→
 post.locals.lookup (ofString "go")=some (.val (.word (0#64)))

private theorem stops_dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
 (body : ProgHOL 64) (different : name≠ofString "go") (child : Stops body) :
 Stops (.dec name shape initializer body) := by
 intro F s post run
 obtain ⟨value,output,_,bodyRun,scope⟩:=evaluate_dec_normal_scope s post name shape initializer body run
 have stopped:=child _ output bodyRun
 rw [scope]
 change (HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)).lookup _=_
 rw [restore_other_local _ name (ofString "go") _ (Ne.symm different)]
 exact stopped

/-- A normally completed null-node iteration leaves the actual loop control
at zero, even though the leaf constructor remains an opaque call here. -/
theorem mpt_insert_null_step_stops {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
 rw [evaluate_mptInsert_null_step s node] at run
 have selected : Stops mptInsertNullStep := by
  unfold mptInsertNullStep
  apply stops_dec _ _ _ _ (by decide)
  apply stops_dec _ _ _ _ (by decide)
  apply stops_dec _ _ _ _ (by decide)
  apply stops_dec _ _ _ _ (by decide)
  intro F initial output normal
  change evaluateHOLFiniteState initial (.seq (.assign .local (ofString "go") (.const (0#64)))
   (.seq mptInsertNewLeafCall mptInsertFinish))=(none,output) at normal
  rw [evaluateHOLFiniteState_seq_line780] at normal
  cases reset : evaluateHOLFiniteState initial (.assign .local (ofString "go") (.const (0#64))) with
  | mk result middle =>
   rw [reset] at normal
   cases result with
   | some result => cases normal
   | none =>
    dsimp only at normal
    obtain ⟨value,evaluated,updated⟩:=evaluate_local_assign_normal_value initial middle (ofString "go") (.const (0#64)) reset
    have equal : value=.val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
    subst value
    have kept:=evaluate_avoidsLocal_flowing (ofString "go") (.seq mptInsertNewLeafCall mptInsertFinish)
     (by rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];rfl) middle
    rw [normal] at kept
    rw [kept (Or.inl rfl),updated]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 exact selected s post run

theorem mpt_insert_null_step_no_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64)))) :
 (evaluateHOLFiniteState s mptInsertLoopStep).1≠some .continue := by
 rw [evaluate_mptInsert_null_step s node]
 exact evaluate_noTopContinue mptInsertNullStep
  (by simp only [mptInsertNullStep,noTopContinue,mptInsertNewLeafCall,source_mptInsert_finish,
   source_mptInsert_commit,source_mptInsert_advance];rfl) s

theorem mpt_insert_null_step_no_break {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : s.locals.lookup (ofString "node")=some (.val (.word (0#64)))) :
 (evaluateHOLFiniteState s mptInsertLoopStep).1≠some .break := by
 rw [evaluate_mptInsert_null_step s node]
 exact evaluate_noTopBreak mptInsertNullStep
  (by simp only [mptInsertNullStep,noTopBreak,mptInsertNewLeafCall,source_mptInsert_finish,
   source_mptInsert_commit,source_mptInsert_advance];rfl) s

#print axioms mpt_insert_null_step_stops
#print axioms mpt_insert_null_step_no_continue
#print axioms mpt_insert_null_step_no_break
end InitECandidate.Runtime
