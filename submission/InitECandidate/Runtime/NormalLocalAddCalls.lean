import InitECandidate.Runtime.NormalLocalAdd
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem normalLocalAdd_decCall (key name function : MlS) (amount : BitVec 64) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (body : ProgHOL 64) (different : name ≠ key)
    (child : NormalLocalAdd key amount body) : NormalLocalAdd key amount (.decCall name shape function arguments body) := by
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

theorem normalLocalAdd_seq_normal_frame (key : MlS) (amount : BitVec 64) (first second : ProgHOL 64)
    (frame : ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state first = (none,post) → post.locals.lookup key = state.locals.lookup key)
    (tail : NormalLocalAdd key amount second) : NormalLocalAdd key amount (.seq first second) := by
  intro F state post index binding run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [firstRun] at run
    cases result with
    | none => exact tail middle post index ((frame state middle firstRun).trans binding) run
    | some result => cases run

theorem normalLocalAdd_guard (key exception : MlS) (amount : BitVec 64) (condition value : ExpHOL 64)
    (body : ProgHOL 64) (tail : NormalLocalAdd key amount body) :
    NormalLocalAdd key amount (.seq (.ite condition (.raise exception value) .skip) body) := by
  apply normalLocalAdd_seq_normal_frame
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

theorem normalLocalAdd_localCall (key name function : MlS) (amount : BitVec 64) (arguments : List (ExpHOL 64))
    (body : ProgHOL 64) (different : name ≠ key) (tail : NormalLocalAdd key amount body) :
    NormalLocalAdd key amount (.seq (.call (some (some (.local,name),none)) function arguments) body) := by
  apply normalLocalAdd_seq_normal_frame
  · intro F state post run
    have success : (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).1 = none := by
      rw [run]
    have same := evaluate_local_call_success_other_locals state function name arguments success key (Ne.symm different)
    rw [run] at same
    exact same
  · exact tail

#print axioms normalLocalAdd_decCall
#print axioms normalLocalAdd_guard
#print axioms normalLocalAdd_localCall
end InitECandidate.Runtime
