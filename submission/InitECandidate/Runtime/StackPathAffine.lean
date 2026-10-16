import InitECandidate.Runtime.StackPathAffineReturning
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.StackSemStateOps

/-- All constructors discharge their actual-execution affine obligations. -/
theorem pathWork_of_affineIH {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s)
    (ih : AffineIH (2 * limit + 2) limit p s) : AffinePathBound (2 * limit + 2) p s := by
  cases p
  case seq a b =>
    apply pathWork_seq_affine
    · have small := StackSemMeasure.seq_first_size_lt a b
      exact ih a s (.inr ⟨rfl, small⟩) (by omega) bounded
    · intro middle run
      have small := StackSemMeasure.seq_second_size_lt a b
      exact ih b middle (measureLtOfClockLe
        (StackSemEvaluateClock.evaluateClock a s none middle run) small) (by omega)
        (CodeSizeState.of_evaluate run bounded)
  case ite cmp reg ri a b =>
    apply pathWork_if_affine
    · have small := StackSemMeasure.if_first_size_lt cmp reg ri a b
      exact ih a s (.inr ⟨rfl, small⟩) (by omega) bounded
    · have small := StackSemMeasure.if_second_size_lt cmp reg ri a b
      exact ih b s (.inr ⟨rfl, small⟩) (by omega) bounded
  case loop body =>
    have small := StackSemMeasure.loop_body_size_lt body
    apply pathWork_loop_affine
    · omega
    · exact ih body s (.inr ⟨rfl, small⟩) (by omega) bounded
    · intro result middle run continuing positive
      have lower := StackSemEvaluateClock.evaluateClock body s result middle run
      have strict : (decClock middle).clock < s.clock := by simp only [decClock]; omega
      exact ih (.loop body) (decClock middle) (.inl strict) sizeBound
        (CodeSizeState.of_evaluate run bounded).decClock
  case call ret dest handler =>
    rcases ret with _ | ⟨rp,link,l1,l2⟩
    · apply pathWork_tail_affine (2 * limit + 2) limit dest handler s (Nat.le_refl _) bounded
      intro body found positive
      have strict : (decClock s).clock < s.clock := by simp only [decClock]; omega
      exact ih body (decClock s) (.inl strict) (findCode_size s bounded dest s.regs body found) bounded.decClock
    · exact pathWork_return_affine (2 * limit + 2) limit rp link l1 l2 dest handler s
        (Nat.le_refl _) sizeBound bounded ih
  case jumpLower r1 r2 dest =>
    apply pathWork_jump_affine (2 * limit + 2) limit r1 r2 dest s (Nat.le_refl _) bounded
    intro body found positive
    have strict : (decClock s).clock < s.clock := by simp only [decClock]; omega
    exact ih body (decClock s) (.inl strict) (findCode_size s bounded (.inl dest) s.regs body found) bounded.decClock
  case rawCall dest =>
    apply pathWork_raw_affine (2 * limit + 2) limit dest s (Nat.le_refl _) bounded
    intro first body found positive
    have procSize := bounded.code dest (.seq first body) found
    have small := StackSemMeasure.seq_second_size_lt first body
    have strict : (decClock s).clock < s.clock := by simp only [decClock]; omega
    exact ih body (decClock s) (.inl strict) (by omega) bounded.decClock
  all_goals apply pathWork_leaf_affine; rfl

/-- Full affine work bound for actual nonerror executions, without recursive
assumptions. The multiplier and syntax potential depend only on bounded code. -/
theorem pathWork_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s) :
    AffinePathBound (2 * limit + 2) p s := by
  exact (measureLtWf.induction
    (C := fun a => sizeOf a.1 ≤ limit → CodeSizeState limit a.2 → AffinePathBound (2 * limit + 2) a.1 a.2)
    (p, s) fun a ih small code => pathWork_of_affineIH limit a.1 a.2 small code
      (fun child next lower childSize nextCode => ih (child,next) lower childSize nextCode)) sizeBound bounded

/-- A simple initial-fuel ceiling follows from the stronger consumed-clock bound. -/
theorem pathWork_affine_fuel {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (notError : result ≠ some .error) :
    pathWork p s ≤ (2 * limit + 2) * s.clock + 2 * limit := by
  have precise := pathWork_affine limit p s sizeBound bounded result post run notError
  have clock := Nat.mul_le_mul_left (2 * limit + 2) (Nat.sub_le s.clock post.clock)
  have potential := Nat.mul_le_mul_left 2 sizeBound
  omega

/-- The compiler simulation itself has an affine source-fuel bound. All original
semantic and compilation premises remain in BoundedFlattenProp. -/
theorem flatten_program_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s) :
    BoundedFlattenProp p s ((2 * limit + 2) * s.clock + 2 * limit) := by
  intro tail result post sid nextLabel continues breaks target hyps
  exact boundedFlattenConcl_mono
    (pathWork_affine_fuel limit p s sizeBound bounded result post hyps.1 hyps.2.1)
    (pathWork_correct p s tail result post sid nextLabel continues breaks target hyps)

#print axioms flatten_program_affine

#print axioms pathWork_of_affineIH
#print axioms pathWork_affine
#print axioms pathWork_affine_fuel
end InitECandidate.Runtime.StackToLab
