import InitE.SourceSemantics
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A source body with no loop, function call, or explicit clock tick. This
predicate is checked on the authoritative HOL-shaped program, not a surrogate VM. -/
def straightLine {width : Nat} [NeZero width] : ProgHOL width → Bool
  | .dec _ _ _ body => straightLine body
  | .seq first second => straightLine first && straightLine second
  | .ite _ yes no => straightLine yes && straightLine no
  | .skip | .break | .continue | .annot _ _ => true
  | .assign _ _ _ | .store _ _ | .raise _ _ | .return _ => true
  | _ => false

/-- Calls and loops are the source clock currency. Straight-line evaluation
preserves it, even if an expression fails or a language exception is raised. -/
def ClockPreserving {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) : Prop :=
  ∀ state : PanSemStateFiniteExact width σ,
    (evaluateHOLFiniteState state program).2.clock = state.clock

section
variable {width : Nat} {σ : Type} [NeZero width]

theorem clockPreserving_skip : ClockPreserving (σ := σ) (.skip : ProgHOL width) := by
  intro state
  rw [evaluateHOLFiniteState_skip]

theorem clockPreserving_assign (kind : VarKind) (name : MlS) (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.assign kind name value) := by
  intro state
  rw [evaluateHOLFiniteState_assign]
  split <;> try rfl
  split
  · cases kind <;> rfl
  · rfl

theorem clockPreserving_store (destination value : ExpHOL width) :
    ClockPreserving (σ := σ) (.store destination value) := by
  intro state
  rw [evaluateHOLFiniteState_store]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem clockPreserving_return (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.return value) := by
  intro state
  rw [evaluateHOLFiniteState_return]
  split <;> try rfl
  split <;> rfl

theorem clockPreserving_raise (name : MlS) (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.raise name value) := by
  intro state
  rw [evaluateHOLFiniteState_raise]
  split <;> try rfl
  dsimp only
  split <;> rfl

theorem clockPreserving_seq (first second : ProgHOL width)
    (one : ClockPreserving (σ := σ) first) (two : ClockPreserving (σ := σ) second) :
    ClockPreserving (σ := σ) (.seq first second) := by
  intro state
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  have fixed : fixClockHOLFinite state (evaluateHOLFiniteState state first) =
      evaluateHOLFiniteState state first := by
    exact fixClockHOLFinite_evaluateState state first
  rw [fixed]
  split
  · exact (two _).trans (one state)
  · exact one state

theorem clockPreserving_ite (condition : ExpHOL width) (yes no : ProgHOL width)
    (hy : ClockPreserving (σ := σ) yes) (hn : ClockPreserving (σ := σ) no) :
    ClockPreserving (σ := σ) (.ite condition yes no) := by
  intro state
  rw [evaluateHOLFiniteState_ite]
  split <;> try rfl
  split
  · exact hn state
  · exact hy state

theorem clockPreserving_dec (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (h : ClockPreserving (σ := σ) body) :
    ClockPreserving (σ := σ) (.dec name shape initializer body) := by
  intro state
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split <;> try rfl
  split
  · exact (h _).trans (by rfl)
  · rfl

/-- Structural certificate for zero source-clock consumption. -/
theorem clockPreserving_of_straightLine (program : ProgHOL width)
    (supported : straightLine program = true) : ClockPreserving (σ := σ) program := by
  cases hprogram : program with
  | skip => exact clockPreserving_skip
  | dec name shape initializer body =>
    exact clockPreserving_dec name shape initializer body
      (clockPreserving_of_straightLine body (by simpa [hprogram, straightLine] using supported))
  | assign kind name value => exact clockPreserving_assign kind name value
  | store destination value => exact clockPreserving_store destination value
  | seq first second =>
    have pieces : straightLine first = true ∧ straightLine second = true := by
      simpa only [hprogram, straightLine, Bool.and_eq_true] using supported
    exact clockPreserving_seq first second (clockPreserving_of_straightLine first pieces.1)
      (clockPreserving_of_straightLine second pieces.2)
  | ite condition yes no =>
    have pieces : straightLine yes = true ∧ straightLine no = true := by
      simpa only [hprogram, straightLine, Bool.and_eq_true] using supported
    exact clockPreserving_ite condition yes no (clockPreserving_of_straightLine yes pieces.1)
      (clockPreserving_of_straightLine no pieces.2)
  | «break» => intro state; rw [evaluateHOLFiniteState_break]
  | «continue» => intro state; rw [evaluateHOLFiniteState_continue]
  | annot tag text => intro state; rw [evaluateHOLFiniteState_annot]
  | raise name value => exact clockPreserving_raise name value
  | «return» value => exact clockPreserving_return value
  | _ => simp [hprogram, straightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

end
/-- The exact declaration codec used by the challenge/compiler. -/
def sourceFunctionBody (declaration : Flapjack.Decl (BitVec 64)) : ProgHOL 64 :=
  match declToHOL declaration with
  | .function function => function.body
  | _ => .skip

theorem chargeGas_straightLine :
    straightLine (sourceFunctionBody Guest.guestFn_charge_gas) = true := by decide_cbv

theorem checkGas_straightLine :
    straightLine (sourceFunctionBody Guest.guestFn_check_gas) = true := by decide_cbv

theorem frameStateGasUsed_straightLine :
    straightLine (sourceFunctionBody Guest.guestFn_frame_state_gas_used) = true := by decide_cbv

/-- Uniform over all concrete source states: no loop/call fuel is consumed in
this helper body. Its caller's entry decrement is accounted separately. -/
theorem chargeGas_clock_preserving : ClockPreserving (σ := Guest.HostMemory)
    (sourceFunctionBody Guest.guestFn_charge_gas) :=
  clockPreserving_of_straightLine _ chargeGas_straightLine

theorem checkGas_clock_preserving : ClockPreserving (σ := Guest.HostMemory)
    (sourceFunctionBody Guest.guestFn_check_gas) :=
  clockPreserving_of_straightLine _ checkGas_straightLine

theorem frameStateGasUsed_clock_preserving : ClockPreserving (σ := Guest.HostMemory)
    (sourceFunctionBody Guest.guestFn_frame_state_gas_used) :=
  clockPreserving_of_straightLine _ frameStateGasUsed_straightLine

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.chargeGas_clock_preserving
