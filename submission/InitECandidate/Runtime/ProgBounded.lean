import InitECandidate.Runtime.ExtStraightLine
import InitECandidate.Runtime.PanCallBoundCombinators
import InitECandidate.Runtime.PanSequenceCodeBound
import InitECandidate.Runtime.AllocationFragmentBound
import InitECandidate.Runtime.LookupCodeInstalledBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every evaluation from the original code with at least `cost` clock spends
at most `cost` ticks and never times out. -/
def ProgBounded (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode → cost ≤ state.clock →
    state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost ∧
      (evaluateHOLFiniteState state program).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state program).1 ≠ some .timeOut

/-- The installed original body of `function` is bounded by `cost`. -/
def FunBounded (function : MlS) (cost : Nat) : Prop :=
  ∃ parameters body returnShape, originalRuntimeCode.lookup function = some (parameters,body,returnShape) ∧
    ProgBounded body cost

namespace ProgBounded

theorem weaken {program : ProgHOL 64} {cost larger : Nat} (bounded : ProgBounded program cost)
    (le : cost ≤ larger) : ProgBounded program larger := by
  intro F state code budget
  obtain ⟨a,b,c⟩ := bounded state code (by omega)
  exact ⟨by omega,b,c⟩

theorem straight (program : ProgHOL 64) (supported : extStraightLine program = true) : ProgBounded program 0 := by
  intro F state _ _
  have clock := clockPreserving_of_extStraightLine (F := F) program supported state
  exact ⟨by omega,by omega,evaluate_extStraightLine_no_timeout program supported state⟩

theorem seq {first tail : ProgHOL 64} {a b : Nat} (left : ProgBounded first a) (right : ProgBounded tail b) :
    ProgBounded (.seq first tail) (a + b) := by
  intro F state code budget
  exact evaluate_sequence_code_bounded state first tail a b (left state code (by omega))
    (fun next nextCode nextBudget => right next (nextCode.trans code) nextBudget) budget

theorem ite (condition : ExpHOL 64) {yes no : ProgHOL 64} {cost : Nat}
    (left : ProgBounded yes cost) (right : ProgBounded no cost) :
    ProgBounded (.ite condition yes no) cost := by
  intro F state code budget
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact right state code budget
    · exact left state code budget
  · simp

theorem dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
    (inner : ProgBounded body cost) : ProgBounded (.dec name shape initializer body) cost := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i value _
    split
    · exact inner (setVarHOLFinite name value state) code budget
    · simp

theorem alloc (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ProgBounded (.call (some (destination,none)) (ofString "alloc") arguments) 2 := by
  intro F state code budget
  exact evaluate_alloc_uniform_call_bounded state destination arguments code budget

theorem bodies_of_fun {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (budget : cost + 1 ≤ state.clock) :
    ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut := by
  obtain ⟨parameters,installedBody,returnShape,lookup,bounded⟩ := installed
  intro values body locals foundShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters installedBody body
    returnShape foundShape values locals (by rw [code]; exact lookup) found
  subst same
  exact bounded (callEntryStateHOLFinite state locals) code (by change cost ≤ state.clock - 1; omega)

theorem call {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ProgBounded (.call (some (destination,none)) function arguments) (cost + 1) := by
  intro F state code budget
  exact evaluate_uniformCallee_call_bounded state function destination arguments cost budget
    (bodies_of_fun installed state code budget)

theorem tail {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    (arguments : List (ExpHOL 64)) :
    ProgBounded (.call none function arguments) (cost + 1) := by
  intro F state code budget
  exact evaluate_tailCall_uniform_bounded state function arguments cost budget
    (bodies_of_fun installed state code budget)

theorem decCall {function : MlS} {cost tailCost : Nat} (installed : FunBounded function cost)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (rest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape function arguments continuation) (cost + 1 + tailCost) := by
  intro F state code budget
  exact evaluate_decCall_uniform_bounded state name function shape arguments continuation cost tailCost budget
    (bodies_of_fun installed state code (by omega))
    (fun next nextCode nextBudget => rest next (nextCode.trans code) nextBudget)

end ProgBounded

/-- A bounded call wrapper for any destination and arguments. -/
theorem FunBounded.call_bounded {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (code : state.code = originalRuntimeCode) (budget : cost + 1 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    state.clock ≤ result.2.clock + (cost + 1) ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut :=
  ProgBounded.call installed destination arguments state code budget

#print axioms ProgBounded.seq
#print axioms ProgBounded.ite
#print axioms ProgBounded.dec
#print axioms ProgBounded.call
#print axioms ProgBounded.tail
#print axioms ProgBounded.decCall
#print axioms FunBounded.call_bounded
end InitECandidate.Runtime
