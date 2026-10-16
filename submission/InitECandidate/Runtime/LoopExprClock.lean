import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
namespace InitECandidate.Runtime
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- Clock bound for the straight-line syntax emitted by Crep expressions.
A conditional charges its one live-set cut; primitive computations charge zero. -/
def loopExprFuel {width : Nat} [NeZero width] : HolLoopProg width → Option Nat
  | .skip | .assign _ _ | .loadByte _ _ | .load32 _ _ | .arith _ => some 0
  | .break _ | .continue _ | .raise _ | .return _ | .setGlobal _ _ => some 0
  | .tick => some 1
  | .seq a b => do return (← loopExprFuel a) + (← loopExprFuel b)
  | .ite _ _ _ a b _ => do return (← loopExprFuel a) + (← loopExprFuel b) + 1
  | .mark body => loopExprFuel body
  | _ => none

theorem cutRes_clock_cost {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (result : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    result.2.clock ≤ (cutRes live result).2.clock + 1 := by
  rcases result with ⟨result,s⟩
  cases result with
  | some _ => simp [cutRes]
  | none =>
    simp only [cutRes]
    cases cut : cutState live s with
    | none => simp
    | some next =>
      have same := cutState_clock cut
      simp only
      split <;> simp only [decClock] <;> omega

/-- Actual execution consumes at most the certified straight-line clock budget,
including error outcomes. This is a bound on the authoritative Loop evaluator. -/
theorem loopExprFuel_correct {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) (fuel : Nat)
    (supported : loopExprFuel p = some fuel) :
    s.clock ≤ (evaluate p s).2.clock + fuel := by
  cases p
  case seq a b =>
    simp only [loopExprFuel, Option.bind_eq_bind] at supported
    cases ca : loopExprFuel a with
    | none => simp [ca] at supported
    | some fa =>
      cases cb : loopExprFuel b with
      | none => simp [ca,cb] at supported
      | some fb =>
        simp [ca,cb] at supported
        subst fuel
        have first := loopExprFuel_correct a s fa ca
        rw [evaluate,fix_clock_evaluate]
        rcases run : evaluate a s with ⟨result,middle⟩
        rw [run] at first
        dsimp only at first
        cases result
        · have second := loopExprFuel_correct b middle fb cb
          change s.clock ≤ (evaluate b middle).2.clock + (fa + fb)
          omega
        · change s.clock ≤ middle.clock + (fa + fb)
          omega
  case ite cmp reg ri a b live =>
    cases ca : loopExprFuel a with
    | none => simp [loopExprFuel,ca] at supported
    | some fa =>
      cases cb : loopExprFuel b with
      | none => simp [loopExprFuel,ca,cb] at supported
      | some fb =>
        simp [loopExprFuel,ca,cb] at supported
        subst fuel
        have first := loopExprFuel_correct a s fa ca
        have second := loopExprFuel_correct b s fb cb
        have cutA := cutRes_clock_cost live (evaluate a s)
        have cutB := cutRes_clock_cost live (evaluate b s)
        rw [evaluate]
        repeat' first | omega | (dsimp only) | split
  case mark body =>
    simpa only [evaluate] using loopExprFuel_correct body s fuel supported
  case arith op =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split
    · simp
    · rename_i next computed
      have same := loopArith_clock computed
      simpa only [Nat.add_zero] using Nat.le_of_eq same.symm
  case assign reg value =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split <;> simp [setVar]
  case loadByte reg address =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    repeat' first | (simp [setVar]) | split
  case load32 reg address =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    repeat' first | (simp [setVar]) | split
  case «return» regs =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split <;> simp [LoopSemStateFiniteExact.callEnv]
  case «raise» reg =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split <;> simp [LoopSemStateFiniteExact.callEnv]
  case setGlobal reg value =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split <;> simp [setGlobals]
  case «break» label => simp [loopExprFuel,evaluate] at supported ⊢
  case «continue» label => simp [loopExprFuel,evaluate] at supported ⊢
  case tick =>
    simp only [loopExprFuel,Option.some.injEq] at supported
    subst fuel
    rw [evaluate]
    split <;> simp only [decClock] <;> omega
  case skip => simp [evaluate,loopExprFuel] at supported ⊢
  all_goals simp [loopExprFuel] at supported
termination_by sizeOf p
decreasing_by all_goals simp_all <;> omega

#print axioms cutRes_clock_cost
#print axioms loopExprFuel_correct
end InitECandidate.Runtime
