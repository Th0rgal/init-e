import InitECandidate.Runtime.StackPathAffineLoop
import InitECandidate.Runtime.StackWorkCeilingControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- One source call tick pays for callee syntax plus the local overhead. -/
theorem affine_tick_funding (rate fuel post work bodySize parentSize : Nat)
    (positive : fuel ≠ 0) (clock : post ≤ fuel - 1)
    (child : work ≤ rate * ((fuel - 1) - post) + 2 * bodySize)
    (funding : 2 * bodySize + 2 ≤ rate) :
    2 + work ≤ rate * (fuel - post) + 2 * parentSize := by
  have elapsed : fuel - post = 1 + ((fuel - 1) - post) := by omega
  rw [elapsed, Nat.mul_add, Nat.mul_one]
  omega

/-- Valid tail calls have an affine work bound funded by their actual call tick.
The source nonerror guard excludes malformed handler and code selections. -/
theorem pathWork_tail_affine {width : Nat} [NeZero width] {C F : Type}
    (rate limit : Nat) (dest : Nat ⊕ Nat) (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) (rateEnough : 2 * limit + 2 ≤ rate)
    (bounded : CodeSizeState limit s)
    (next : ∀ body, findCode dest s.regs s.code = some body → s.clock ≠ 0 →
      AffinePathBound rate body (decClock s)) : AffinePathBound rate (.call none dest handler) s := by
  intro result post run notError
  have err : ∀ {bad : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, bad) = (result, post) → False :=
    fun eq => notError (Prod.mk.inj eq).1.symm
  rw [StackSemEvaluate.evaluate_call] at run
  dsimp only at run
  cases found : findCode dest s.regs s.code with
  | none => rw [found] at run; exact (err run).elim
  | some body =>
    rw [found] at run
    cases handler with
    | some h => exact (err run).elim
    | none =>
      dsimp only at run
      by_cases zero : s.clock = 0
      · rw [if_pos zero] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        rw [pathWork, if_pos zero]
        have positive := prog_size_positive (.call none dest none : HolProg width)
        simp only [emptyEnv]
        omega
      · rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
        cases bodyRun : StackSemEvaluate.evaluate (body, decClock s) with
        | mk bodyResult middle =>
          rw [bodyRun] at run
          dsimp only at run
          by_cases bad : badFunReturn bodyResult = true
          · rw [if_pos bad] at run; exact (err run).elim
          · rw [if_neg bad] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            have child := next body found zero bodyResult middle bodyRun notError
            have clock := StackSemEvaluateClock.evaluateClock body (decClock s) bodyResult middle bodyRun
            have sizeBound := findCode_size s bounded dest s.regs body found
            rw [pathWork, if_neg zero, found]
            apply affine_tick_funding rate s.clock middle.clock _ (sizeOf body) _ zero
            · exact clock
            · exact child
            · omega

/-- Raw calls pay only for the body selected from an actual sequence procedure. -/
theorem pathWork_raw_affine {width : Nat} [NeZero width] {C F : Type}
    (rate limit dest : Nat) (s : StackSemStateFiniteExact width C F)
    (rateEnough : 2 * limit + 2 ≤ rate) (bounded : CodeSizeState limit s)
    (next : ∀ first body, sptLookup dest s.code = some (.seq first body) → s.clock ≠ 0 →
      AffinePathBound rate body (decClock s)) : AffinePathBound rate (.rawCall dest) s := by
  intro result post run notError
  have err : ∀ {bad : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, bad) = (result, post) → False :=
    fun eq => notError (Prod.mk.inj eq).1.symm
  rw [StackSemEvaluate.evaluate_rawCall] at run
  cases found : sptLookup dest s.code with
  | none => rw [found] at run; exact (err run).elim
  | some proc =>
    rw [found] at run
    cases proc
    case seq first body =>
      simp only [Flapjack.StackSemControl.destSeq] at run
      by_cases zero : s.clock = 0
      · rw [if_pos zero] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        rw [pathWork, if_pos zero]
        have positive := prog_size_positive (.rawCall dest : HolProg width)
        omega
      · rw [if_neg zero] at run
        cases bodyRun : StackSemEvaluate.evaluate (body, decClock s) with
        | mk bodyResult middle =>
          rw [bodyRun] at run
          dsimp only at run
          by_cases bad : badFunReturn bodyResult = true
          · rw [if_pos bad] at run; exact (err run).elim
          · rw [if_neg bad] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            have child := next first body found zero bodyResult middle bodyRun notError
            have clock := StackSemEvaluateClock.evaluateClock body (decClock s) bodyResult middle bodyRun
            have procSize := bounded.code dest (.seq first body) found
            have childSize := StackSemMeasure.seq_second_size_lt first body
            rw [pathWork, if_neg zero, found]
            apply affine_tick_funding rate s.clock middle.clock _ (sizeOf body) _ zero
            · exact clock
            · exact child
            · omega
    all_goals simp only [Flapjack.StackSemControl.destSeq] at run; exact (err run).elim

/-- Only a taken jump contributes body work or consumes a source call tick. -/
theorem pathWork_jump_affine {width : Nat} [NeZero width] {C F : Type}
    (rate limit r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F)
    (rateEnough : 2 * limit + 2 ≤ rate) (bounded : CodeSizeState limit s)
    (next : ∀ body, findCode (.inl dest) s.regs s.code = some body → s.clock ≠ 0 →
      AffinePathBound rate body (decClock s)) : AffinePathBound rate (.jumpLower r1 r2 dest) s := by
  intro result post run notError
  have err : ∀ {bad : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, bad) = (result, post) → False :=
    fun eq => notError (Prod.mk.inj eq).1.symm
  rw [StackSemEvaluate.evaluate_jumpLower] at run
  rcases hx : getVar r1 s with _ | ⟨x | ⟨_, _⟩⟩ <;>
    rcases hy : getVar r2 s with _ | ⟨y | ⟨_, _⟩⟩ <;>
    simp only [hx, hy] at run <;> try exact (err run).elim
  by_cases lower : wordCmpHOL .lower x y = true
  · rw [if_pos lower] at run
    cases found : findCode (.inl dest) s.regs s.code with
    | none => rw [found] at run; exact (err run).elim
    | some body =>
      rw [found] at run
      dsimp only at run
      by_cases zero : s.clock = 0
      · rw [if_pos zero] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        rw [pathWork]
        simp only [hx, hy, lower, ↓reduceIte, if_pos zero]
        have positive := prog_size_positive (.jumpLower r1 r2 dest : HolProg width)
        omega
      · rw [if_neg zero] at run
        cases bodyRun : StackSemEvaluate.evaluate (body, decClock s) with
        | mk bodyResult middle =>
          rw [bodyRun] at run
          dsimp only at run
          by_cases bad : badFunReturn bodyResult = true
          · rw [if_pos bad] at run; exact (err run).elim
          · rw [if_neg bad] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            have child := next body found zero bodyResult middle bodyRun notError
            have clock := StackSemEvaluateClock.evaluateClock body (decClock s) bodyResult middle bodyRun
            have sizeBound := findCode_size s bounded (.inl dest) s.regs body found
            rw [pathWork]
            simp only [hx, hy, lower, ↓reduceIte, if_neg zero, found]
            apply affine_tick_funding rate s.clock middle.clock _ (sizeOf body) _ zero
            · exact clock
            · exact child
            · omega
  · have stopped : wordCmpHOL .lower x y = false := by simpa using lower
    rw [pathWork]
    simp only [hx, hy, stopped, Bool.false_eq_true, if_false]
    have positive := prog_size_positive (.jumpLower r1 r2 dest : HolProg width)
    omega

#print axioms pathWork_raw_affine
#print axioms pathWork_jump_affine

#print axioms affine_tick_funding
#print axioms pathWork_tail_affine
end InitECandidate.Runtime.StackToLab
