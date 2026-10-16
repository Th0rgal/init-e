import InitECandidate.Runtime.WordWork

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

theorem wordWork_seq {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordWork (.seq first second) source = 1 + wordWork first source +
      (match evaluate first source with
       | (none, middle) => wordWork second middle
       | _ => 0) := by
  rw [wordWork, fix_clock_evaluate]
  cases run : evaluate first source with
  | mk result middle => cases result <;> rfl

theorem seq_first_work_le {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordWork first source ≤ wordWork (.seq first second) source := by
  rw [wordWork_seq]
  omega

/-- The second budget is needed only at the actual successful first successor. -/
theorem seq_work_sum_le {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (source middle : WordSemStateFiniteExact width C F)
    (run : evaluate first source = (none, middle)) :
    wordWork first source + wordWork second middle ≤ wordWork (.seq first second) source := by
  rw [wordWork_seq, run]
  dsimp only
  omega

theorem wordWork_if {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordWork (.ite cmp reg operand first second) source =
      1 + wordWork first source + wordWork second source := by rw [wordWork]

theorem if_first_work_le {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordWork first source ≤ wordWork (.ite cmp reg operand first second) source := by
  rw [wordWork_if]
  omega

theorem if_second_work_le {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordWork second source ≤ wordWork (.ite cmp reg operand first second) source := by
  rw [wordWork_if]
  omega

#print axioms seq_work_sum_le
end InitECandidate.Runtime.WordToStack
