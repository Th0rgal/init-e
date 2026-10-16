import InitECandidate.Runtime.StackWorkCeilingCalls
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

theorem stackWork_of_ceilingIH {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s) (ih : CeilingIH limit p s) :
    stackWork p s ≤ workCeiling limit s.clock (sizeOf p) := by
  cases p
  case seq a b => exact stackWork_seq_ceiling limit a b s sizeBound bounded ih
  case ite cmp r ri a b => exact stackWork_if_ceiling limit cmp r ri a b s sizeBound bounded ih
  case loop body => exact stackWork_loop_ceiling limit body s sizeBound bounded ih
  case jumpLower a b dest => exact stackWork_jump_ceiling limit a b dest s bounded ih
  case rawCall dest => exact stackWork_raw_ceiling limit dest s bounded ih
  case call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩
    · exact stackWork_tail_ceiling limit dest handler s bounded ih
    · exact stackWork_returning_ceiling limit rp link l1 l2 dest handler s sizeBound bounded ih
  all_goals rw [stackWork] <;> first | exact two_le_workCeiling _ _ _ | simp

/-- A uniform numerical ceiling for the entire StackToLab work function.
Actual evaluation preserves the bounded code/oracle invariant; no recursive
simulation or runtime work bound is assumed. -/
theorem stackWork_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (bounded : CodeSizeState limit s) :
    stackWork p s ≤ workCeiling limit s.clock (sizeOf p) := by
  have children : CeilingIH limit p s := by
    intro child next smaller small nextBounded
    exact Nat.le_trans (stackWork_ceiling limit child next small nextBounded)
      (workCeiling_child limit s.clock next.clock (sizeOf p) (sizeOf child) smaller)
  exact stackWork_of_ceilingIH limit p s sizeBound bounded children
termination_by workRank limit s.clock (sizeOf p)

#print axioms stackWork_of_ceilingIH
#print axioms stackWork_ceiling
end InitECandidate.Runtime.StackToLab
