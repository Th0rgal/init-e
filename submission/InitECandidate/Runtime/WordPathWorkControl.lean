import InitECandidate.Runtime.WordPathWork

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

theorem wordPathWork_seq {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordPathWork (.seq first second) source = 1 + wordPathWork first source +
      (match evaluate first source with
       | (none, middle) => wordPathWork second middle
       | _ => 0) := by
  rw [wordPathWork, fix_clock_evaluate]
  cases run : evaluate first source with
  | mk result middle => cases result <;> rfl

theorem seq_first_work_le_path {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordPathWork first source ≤ wordPathWork (.seq first second) source := by
  rw [wordPathWork_seq]
  omega

/-- The second budget is needed only at the actual successful first successor. -/
theorem seq_work_sum_le_path {width : Nat} [NeZero width] {C F : Type}
    (first second : WordLangProgHOL (BitVec width))
    (source middle : WordSemStateFiniteExact width C F)
    (run : evaluate first source = (none, middle)) :
    wordPathWork first source + wordPathWork second middle ≤ wordPathWork (.seq first second) source := by
  rw [wordPathWork_seq, run]
  dsimp only
  omega

theorem if_first_work_le_path {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F)
    (x y : WordLocW width) (left : getVar reg source = some x) (right : getVarImm operand source = some y)
    (chosen : wordSemWordCmp cmp x y = some true) :
    wordPathWork first source ≤ wordPathWork (.ite cmp reg operand first second) source := by
  rw [wordPathWork]
  simp only [left, right, chosen]
  omega

theorem if_second_work_le_path {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F)
    (x y : WordLocW width) (left : getVar reg source = some x) (right : getVarImm operand source = some y)
    (chosen : wordSemWordCmp cmp x y = some false) :
    wordPathWork second source ≤ wordPathWork (.ite cmp reg operand first second) source := by
  rw [wordPathWork]
  simp only [left, right, chosen]
  omega

#print axioms seq_work_sum_le_path
end InitECandidate.Runtime.WordToStack
