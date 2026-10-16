import InitECandidate.Runtime.StackWork
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- The finite syntax-only work budget of the zero-clock slice. -/
def zeroStackWork {width : Nat} [NeZero width] : HolProg width → Nat
  | .seq a b => 2 + zeroStackWork a + zeroStackWork b
  | .ite _ _ _ a b => 2 + zeroStackWork a + zeroStackWork b
  | .loop body => 2 + zeroStackWork body
  | _ => 2

/-- Zero clock prevents every dynamic call and loop reentry. Even with arbitrary
code, oracles and memory, the actual work reduces to this finite syntax budget. -/
theorem stackWork_zero {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) (zero : s.clock = 0) :
    stackWork prog s = zeroStackWork prog := by
  cases prog
  case seq a b =>
    have lower := StackSemMeasure.fixClock_clock_le s (StackSemEvaluate.evaluate (a, s))
    have nextZero : (fixClock s (StackSemEvaluate.evaluate (a, s))).2.clock = 0 := by omega
    rw [stackWork, zeroStackWork, stackWork_zero a s zero,
      stackWork_zero b _ nextZero]
  case ite cmp r ri a b =>
    rw [stackWork, zeroStackWork, stackWork_zero a s zero, stackWork_zero b s zero]
  case loop body =>
    have lower := StackSemMeasure.fixClock_clock_le s (StackSemEvaluate.evaluate (body, s))
    have nextZero : (fixClock s (StackSemEvaluate.evaluate (body, s))).2.clock = 0 := by omega
    rw [stackWork, zeroStackWork, stackWork_zero body s zero]
    simp [nextZero]
  case call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩ <;> simp [stackWork, zeroStackWork, zero]
  all_goals simp [stackWork, zeroStackWork, zero]
termination_by sizeOf prog

#print axioms stackWork_zero
end InitECandidate.Runtime.StackToLab
