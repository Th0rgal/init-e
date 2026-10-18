import InitECandidate.Runtime.NormalLocalIncrement
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem normalLocalIncrement_decCall (key name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (body : ProgHOL 64) (different : name ≠ key)
    (child : NormalLocalIncrement key body) : NormalLocalIncrement key (.decCall name shape function arguments body) := by
  intro F state post index binding run
  obtain ⟨value,ready,output,locals,bodyRun,scope⟩ :=
    evaluate_decCall_unconditional_normal_scope state post name function shape arguments body run
  have entered : (setVarHOLFinite name value ready).locals.lookup key = some (.val (.word index)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different,locals] using binding
  have advanced := child _ output index entered bodyRun
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup key = _
  rw [restore_other_local _ name key _ (Ne.symm different)]
  exact advanced

theorem normalLocalIncrement_seq_normal_frame (key : MlS) (first second : ProgHOL 64)
    (frame : ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state first = (none,post) → post.locals.lookup key = state.locals.lookup key)
    (tail : NormalLocalIncrement key second) : NormalLocalIncrement key (.seq first second) := by
  intro F state post index binding run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [firstRun] at run
    cases result with
    | none => exact tail middle post index ((frame state middle firstRun).trans binding) run
    | some result => cases run

theorem normalLocalIncrement_guard (key exception : MlS) (condition value : ExpHOL 64)
    (body : ProgHOL 64) (tail : NormalLocalIncrement key body) :
    NormalLocalIncrement key (.seq (.ite condition (.raise exception value) .skip) body) := by
  apply normalLocalIncrement_seq_normal_frame
  · intro F state post run
    have terminal := evaluate_raise_terminal state exception value
    rw [evaluateHOLFiniteState_ite] at run
    split at run
    · split at run
      · rw [evaluateHOLFiniteState_skip] at run
        have same := (Prod.mk.inj run).2
        simpa only [same] using (Eq.refl (state.locals.lookup key))
      · rw [run] at terminal
        exact False.elim (terminal rfl)
    · cases run
  · exact tail

theorem normalLocalIncrement_localCall (key name function : MlS) (arguments : List (ExpHOL 64))
    (body : ProgHOL 64) (different : name ≠ key) (tail : NormalLocalIncrement key body) :
    NormalLocalIncrement key (.seq (.call (some (some (.local,name),none)) function arguments) body) := by
  apply normalLocalIncrement_seq_normal_frame
  · intro F state post run
    have success : (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).1 = none := by
      rw [run]
    have same := evaluate_local_call_success_other_locals state function name arguments success key (Ne.symm different)
    rw [run] at same
    exact same
  · exact tail

#print axioms normalLocalIncrement_decCall
#print axioms normalLocalIncrement_guard
#print axioms normalLocalIncrement_localCall
end InitECandidate.Runtime
