import InitECandidate.Runtime.WorkCeiling
import InitECandidate.Runtime.StackWork
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl

abbrev CeilingIH {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ child (next : StackSemStateFiniteExact width C F),
    workRank limit next.clock (sizeOf child) < workRank limit s.clock (sizeOf p) →
    sizeOf child ≤ limit → CodeSizeState limit next →
    stackWork child next ≤ 8 ^ workRank limit s.clock (sizeOf p)

theorem CodeSizeState.evaluated {width : Nat} [NeZero width] {C F : Type}
    {limit : Nat} {s : StackSemStateFiniteExact width C F} (bounded : CodeSizeState limit s)
    (p : HolProg width) : CodeSizeState limit (Flapjack.StackSemControl.fixClock s (StackSemEvaluate.evaluate (p, s))).2 := by
  have next := CodeSizeState.of_evaluate (p := p) (s := s) (t := (StackSemEvaluate.evaluate (p,s)).2)
    (result := (StackSemEvaluate.evaluate (p,s)).1) rfl bounded
  exact ⟨next.code, next.oracle⟩

theorem stackWork_seq_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (a b : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf (.seq a b : HolProg width) ≤ limit) (bounded : CodeSizeState limit s)
    (ih : CeilingIH limit (.seq a b) s) :
    stackWork (.seq a b) s ≤ workCeiling limit s.clock (sizeOf (.seq a b : HolProg width)) := by
  have firstSize := StackSemMeasure.seq_first_size_lt a b
  have secondSize := StackSemMeasure.seq_second_size_lt a b
  have clockLe := StackSemMeasure.fixClock_clock_le s (StackSemEvaluate.evaluate (a,s))
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) firstSize)
    (by omega) bounded
  have second := ih b _ (workRank_subprogram _ _ _ _ _ clockLe secondSize)
    (by omega) (bounded.evaluated a)
  rw [stackWork]
  exact workCeiling_two _ _ _ first second

theorem stackWork_if_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (cmp : Compiler.Encoders.Asm.HolCmp) (r : Nat)
    (ri : Compiler.Encoders.Asm.HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf (.ite cmp r ri a b : HolProg width) ≤ limit) (bounded : CodeSizeState limit s)
    (ih : CeilingIH limit (.ite cmp r ri a b) s) :
    stackWork (.ite cmp r ri a b) s ≤ workCeiling limit s.clock (sizeOf (.ite cmp r ri a b : HolProg width)) := by
  have firstSize := StackSemMeasure.if_first_size_lt cmp r ri a b
  have secondSize := StackSemMeasure.if_second_size_lt cmp r ri a b
  have first := ih a s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) firstSize) (by omega) bounded
  have second := ih b s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) secondSize) (by omega) bounded
  rw [stackWork]
  exact workCeiling_two _ _ _ first second

theorem stackWork_loop_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf (.loop body : HolProg width) ≤ limit) (bounded : CodeSizeState limit s)
    (ih : CeilingIH limit (.loop body) s) :
    stackWork (.loop body) s ≤ workCeiling limit s.clock (sizeOf (.loop body : HolProg width)) := by
  have bodySize := StackSemMeasure.loop_body_size_lt body
  have first := ih body s (workRank_subprogram _ _ _ _ _ (Nat.le_refl _) bodySize) (by omega) bounded
  rw [stackWork]
  split_ifs with continuing
  · have clockLe := StackSemMeasure.fixClock_clock_le s (StackSemEvaluate.evaluate (body,s))
    have positive : (Flapjack.StackSemControl.fixClock s (StackSemEvaluate.evaluate (body,s))).2.clock ≠ 0 := by
      have parts := continuing
      simp only [Bool.and_eq_true, bne_iff_ne] at parts
      exact parts.2
    have smaller : (decClock (Flapjack.StackSemControl.fixClock s (StackSemEvaluate.evaluate (body,s))).2).clock < s.clock := by
      simp only [decClock]
      omega
    have rest := ih (.loop body) _ (workRank_clock _ _ _ _ _ smaller sizeBound) sizeBound
      ((bounded.evaluated body).decClock)
    exact workCeiling_two _ _ _ first rest
  · simpa only [Nat.add_zero, workCeiling] using workCeiling_one _ _ first

#print axioms stackWork_seq_ceiling
#print axioms stackWork_if_ceiling
#print axioms stackWork_loop_ceiling
end InitECandidate.Runtime.StackToLab
