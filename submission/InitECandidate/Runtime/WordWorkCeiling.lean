import InitECandidate.Runtime.WordWorkCeilingReturning
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Every Word constructor has a numerical work ceiling, assuming only the
strictly smaller recursive obligations used by the actual evaluator. -/
theorem wordWork_of_ceilingIH {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL p = true) (ih : WordCeilingIH limit p s) :
    wordWork p s ≤ workCeiling limit s.clock (sizeOf p) := by
  cases p
  case seq a b => exact wordWork_seq_ceiling limit a b s small bounded safe ih
  case ite cmp reg ri a b => exact wordWork_if_ceiling limit cmp reg ri a b s small bounded safe ih
  case loop names body exits => exact wordWork_loop_ceiling limit names exits body s small bounded safe ih
  case call ret dest args handler =>
    rcases ret with _ | ⟨values,names,retCode,l1,l2⟩
    · exact wordWork_tail_ceiling limit dest args handler s bounded ih
    · exact wordWork_return_ceiling limit values names retCode l1 l2 dest args handler s small bounded safe ih
  all_goals rw [wordWork] <;> first | exact Nat.le_trans (by decide : 1 ≤ 2) (two_le_workCeiling _ _ _) | simp

/-- Full uniform numerical WordToStack work bound. Recursive execution
assumptions are discharged by the original clock/syntax ordering. -/
theorem wordWork_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL p = true) :
    wordWork p s ≤ workCeiling limit s.clock (sizeOf p) := by
  have children : WordCeilingIH limit p s := by
    intro child next smaller childSize nextBounded childSafe
    exact Nat.le_trans (wordWork_ceiling limit child next childSize nextBounded childSafe)
      (workCeiling_child limit s.clock next.clock (sizeOf p) (sizeOf child) smaller)
  exact wordWork_of_ceilingIH limit p s small bounded safe children
termination_by workRank limit s.clock (sizeOf p)

#print axioms wordWork_of_ceilingIH
#print axioms wordWork_ceiling
end InitECandidate.Runtime.WordToStack
