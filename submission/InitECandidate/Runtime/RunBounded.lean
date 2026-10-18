import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.PanUniformCalleeCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The evaluation of `program` from this particular state spends at most
`cost` ticks and does not time out, whatever its outcome. -/
def RunBounded {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) (cost : Nat) : Prop :=
  state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost ∧
    (evaluateHOLFiniteState state program).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut

namespace RunBounded

theorem weaken {F : Type} {state : PanSemStateFiniteExact 64 F} {program : ProgHOL 64} {cost larger : Nat}
    (bounded : RunBounded state program cost) (le : cost ≤ larger) : RunBounded state program larger :=
  ⟨by have := bounded.1; omega,bounded.2.1,bounded.2.2⟩

theorem ofProg {F : Type} {state : PanSemStateFiniteExact 64 F} {program : ProgHOL 64} {cost : Nat}
    (bounded : ProgBounded program cost) (code : state.code = originalRuntimeCode) (budget : cost ≤ state.clock) :
    RunBounded state program cost :=
  bounded state code budget

/-- Sequencing: the tail is only needed after a normal first outcome, with the
remaining budget and the unchanged code. -/
theorem seq {F : Type} {state : PanSemStateFiniteExact 64 F} {first tail : ProgHOL 64} {a b : Nat}
    (left : RunBounded state first a) (budget : a + b ≤ state.clock)
    (right : ∀ next, evaluateHOLFiniteState state first = (none,next) → next.code = state.code →
      b ≤ next.clock → RunBounded next tail b) :
    RunBounded state (.seq first tail) (a + b) := by
  have meta' := evaluateHOLFiniteState_metadata state first
  unfold RunBounded at left ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at left meta'
    dsimp only at left meta'
    obtain ⟨l1,l2,l3⟩ := left
    cases result with
    | none =>
      dsimp only
      obtain ⟨r1,r2,r3⟩ := right middle run meta'.1 (by omega)
      exact ⟨by omega,by omega,r3⟩
    | some r =>
      dsimp only
      exact ⟨by omega,l2,l3⟩

/-- A word-constant declaration keeps the clock and outcome of its body. -/
theorem decConst {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (k : BitVec 64)
    {body : ProgHOL 64} {cost : Nat}
    (inner : RunBounded (setVarHOLFinite name (.val (.word k)) state) body cost) :
    RunBounded state (.dec name .one (.const k) body) cost := by
  unfold RunBounded at inner ⊢
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  exact inner

/-- A declared call from a state whose arguments evaluate to `values`: the
looked-up body is bounded from its entry state, and the continuation is bounded
after every returned callee run (resumed with the caller's locals). -/
theorem decCall {F : Type} {state : PanSemStateFiniteExact 64 F} {name function : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {values : List (ValueHOL 64)} {bodyCost tailCost : Nat}
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (budget : bodyCost + 1 + tailCost ≤ state.clock)
    (bodies : ∀ body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      RunBounded (callEntryStateHOLFinite state locals) body bodyCost ∧
      ∀ value post, evaluateHOLFiniteState (callEntryStateHOLFinite state locals) body = (some (.returned value),post) →
        tailCost ≤ post.clock →
        RunBounded (setVarHOLFinite name value {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name shape function arguments continuation) (bodyCost + 1 + tailCost) := by
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
    simp
  | some installed =>
    obtain ⟨body,callee,returnShape⟩ := installed
    obtain ⟨bounded,resume⟩ := bodies body callee returnShape lookup
    unfold RunBounded at bounded
    cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [ran] at bounded
      obtain ⟨spent,kept,safe⟩ := bounded
      change state.clock - 1 ≤ post.clock + bodyCost at spent
      have whole := evaluate_decCall_continuation_bounded state post name function shape returnShape arguments values
        body continuation callee result (bodyCost + 1) tailCost args lookup (by omega) ran kept (by omega) safe
        (by
          intro value returned
          subst returned
          exact resume value post ran (by omega))
      unfold RunBounded
      simpa only [Nat.add_assoc] using whole

/-- A one-word declaration whose initializer evaluates to a word keeps the
clock and outcome of its body. -/
theorem decWord {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (initializer : ExpHOL 64)
    (value : BitVec 64) {body : ProgHOL 64} {cost : Nat}
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      initializer = some (.val (.word value)))
    (inner : RunBounded (setVarHOLFinite name (.val (.word value)) state) body cost) :
    RunBounded state (.dec name .one initializer body) cost := by
  unfold RunBounded at inner ⊢
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [evaluated]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word value))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk]
  exact inner

/-- Any one-word or struct declaration: the body is only needed after an
initializer evaluation that succeeds (other outcomes are clock-free errors). -/
theorem dec {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    {body : ProgHOL 64} {cost : Nat}
    (inner : ∀ value, @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      initializer = some value → RunBounded (setVarHOLFinite name value state) body cost) :
    RunBounded state (.dec name shape initializer body) cost := by
  unfold RunBounded
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i value evaluated
    split
    · exact inner value evaluated
    · simp

/-- A handler-free call from a state whose arguments evaluate to `values`
costs its looked-up body's bound plus the entry tick, in every outcome. -/
theorem call {F : Type} {state : PanSemStateFiniteExact 64 F} {function : MlS}
    {destination : Option (VarKind × MlS)} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)} {bodyCost : Nat}
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      RunBounded (callEntryStateHOLFinite state locals) body bodyCost) :
    RunBounded state (.call (some (destination,none)) function arguments) (bodyCost + 1) := by
  unfold RunBounded
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
  | some installed =>
    obtain ⟨body,callee,returnShape⟩ := installed
    have bounded := bodies body callee returnShape lookup
    unfold RunBounded at bounded
    cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [ran] at bounded
      dsimp only at bounded
      have output := evaluate_call_body_clock_no_timeout state post function destination arguments values body callee
        returnShape result args lookup (by omega) ran bounded.2.2
      rw [output.2]
      have spent : state.clock - 1 ≤ post.clock + bodyCost := bounded.1
      have kept : post.clock ≤ state.clock - 1 := bounded.2.1
      exact ⟨by omega,by omega,output.1⟩

end RunBounded

#print axioms RunBounded.seq
#print axioms RunBounded.decConst
#print axioms RunBounded.decCall
#print axioms RunBounded.decWord
#print axioms RunBounded.dec
#print axioms RunBounded.call
end InitECandidate.Runtime
