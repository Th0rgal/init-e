import InitECandidate.Runtime.WordPathAffineCalls
import InitECandidate.Runtime.WordPathWorkCorrect
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Every Word constructor discharges its affine obligation from strictly
smaller recursive obligations used by the actual evaluator. -/
theorem wordPathWork_of_affineIH {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL p = true) (ih : WordAffineIH limit p s) :
    WordAffine (2 * limit + 2) p s := by
  have positive := word_prog_size_positive p
  cases p
  case seq a b => exact wordPath_seq_affine limit a b s small bounded safe ih
  case ite cmp reg ri a b => exact wordPath_if_affine limit cmp reg ri a b s small bounded safe ih
  case loop names body exits => exact wordPath_loop_affine limit names exits body s small bounded safe ih
  case call ret dest args handler =>
    rcases ret with _ | ⟨values,names,retCode,l1,l2⟩
    · exact wordPath_tail_affine limit dest args handler s bounded ih
    · exact wordPath_return_affine limit values names retCode l1 l2 dest args handler s small bounded safe ih
  all_goals
    intro result post run
    rw [wordPathWork] <;> first | omega | simp

/-- Full affine Word-to-Stack work bound: for every actual execution of bounded
no-install code, selected-path work is at most (2L+2) per consumed source clock
plus twice the program size. No recursive premise remains. -/
theorem wordPathWork_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL p = true) : WordAffine (2 * limit + 2) p s := by
  have children : WordAffineIH limit p s := by
    intro child next smaller childSize nextBounded childSafe
    exact wordPathWork_affine limit child next childSize nextBounded childSafe
  exact wordPathWork_of_affineIH limit p s small bounded safe children
termination_by workRank limit s.clock (sizeOf p)

/-- Initial-fuel form. -/
theorem wordPathWork_affine_fuel {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (small : sizeOf p ≤ limit) (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL p = true) :
    wordPathWork p s ≤ (2 * limit + 2) * s.clock + 2 * limit := by
  cases run : evaluate p s with
  | mk result post =>
    have precise := wordPathWork_affine limit p s small bounded safe result post run
    have clock := Nat.mul_le_mul_left (2 * limit + 2) (Nat.sub_le s.clock post.clock)
    omega

#print axioms wordPathWork_of_affineIH
#print axioms wordPathWork_affine
#print axioms wordPathWork_affine_fuel
end InitECandidate.Runtime.WordToStack
