import InitECandidate.Runtime.StackPathWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Count actual leaf operations; control flow is certified separately. -/
def stackLeaves {width : Nat} [NeZero width] : HolProg width → Nat
  | .seq first second => stackLeaves first + stackLeaves second
  | _ => 1

def stackStraightLine {width : Nat} [NeZero width] : HolProg width → Bool
  | .skip | .inst _ | .stackLoad _ _ | .stackStore _ _ | .get _ _ | .opCurrHeap _ _ _ => true
  | .seq first second => stackStraightLine first && stackStraightLine second
  | _ => false

theorem stack_leaves_positive {width : Nat} [NeZero width] (p : HolProg width) :
    1 ≤ stackLeaves p := by
  cases p <;> simp only [stackLeaves] <;> try omega
  case seq first second =>
    have firstBound := stack_leaves_positive first
    omega
termination_by sizeOf p

/-- Budget follows actual execution and stops charging a sequence after exit. -/
theorem stack_straight_path_bound {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (source : StackSemStateFiniteExact width C F)
    (supported : stackStraightLine p = true) :
    StackToLab.pathWork p source + 2 ≤ 4 * stackLeaves p := by
  cases p <;> simp only [stackStraightLine, Bool.and_eq_true] at supported
  all_goals try contradiction
  all_goals try (simp only [StackToLab.pathWork, stackLeaves]; omega)
  case seq first second =>
    have firstBound := stack_straight_path_bound first source supported.1
    have secondPositive := stack_leaves_positive second
    rw [StackToLab.pathWork]
    simp only [stackLeaves]
    cases run : StackSemControl.fixClock source (StackSemEvaluate.evaluate (first, source)) with
    | mk result middle =>
      cases result with
      | none =>
        have secondBound := stack_straight_path_bound second middle supported.2
        dsimp only
        omega
      | some value => dsimp only; omega
termination_by sizeOf p

#print axioms stack_straight_path_bound
end InitECandidate.Runtime.FineCost
