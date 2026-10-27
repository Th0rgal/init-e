import InitECandidate.Solver.FiniteKBridge
import InitECandidate.Solver.Op3ClockBound
import InitECandidate.Solver.Op3CensusBridge
import InitECandidate.Solver.Op3GuestBridge
import InitECandidate.Solver.HybridScoreBounds

set_option autoImplicit true

namespace InitECandidate.Solver.Op3FiniteKBridge
open InitECandidate.Solver.FiniteKBridge
open InitECandidate.Solver.Op3ClockBound
open InitECandidate.Solver.HybridScoreBounds
open InitE
open Flapjack

/-- Fixed bootstrap prefix supplied by the verified initialisation trace. -/
def bootstrapSteps : Nat := 23077

/-- The explicit monotone transfer used by the finite-K certificate. -/
def T (kSrc : Nat) : Nat := 8 * (10 * (kSrc + 5000))

theorem bootstrapSteps_exact : bootstrapSteps = 23077 := rfl

theorem T_mono : ∀ a b, a ≤ b → T a ≤ T b := by
  intro a b h
  unfold T
  omega

theorem finiteK_clock_shape (G kSrc : Nat) (h : kSrc ≤ G) :
    bootstrapSteps + T kSrc ≤ bootstrapSteps + T G := by
  exact Nat.add_le_add_left (T_mono _ _ h) _

/-- Scaled form of the hybrid score: the requested 0.5 factors are represented
by multiplying the score by two, avoiding non-kernel floating-point arithmetic. -/
def hybridScoreNumerator (blockGas : Nat) (gas : Nat → Nat) (count : Nat) : Nat :=
  50_000_000 / WORST_CASE blockGas + loopSum gas count

theorem hybridScoreNumerator_formula (blockGas : Nat) (gas : Nat → Nat) (count : Nat) :
    hybridScoreNumerator blockGas gas count =
      50_000_000 / WORST_CASE blockGas +
        (List.range count).foldl (fun acc i => acc + gas i / WORST_CASE i) 0 := rfl

end InitECandidate.Solver.Op3FiniteKBridge

namespace InitECandidate.Solver.Op3FiniteKBridge
open InitECandidate.Solver.FiniteKBridge
open InitE
open Flapjack

/-- Specialization of the finite-K bridge at the verified aggregate source bound. -/
theorem certificate_at_aggregate_bound (s : Submission)
    (score : s.K = .finite (23077 + T 459564194)) (admitted : s.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL s.machineConfig (sourceFfi input)
        (s.initialState input) behaviour → behaviour = .terminate outcome events)
    (transfer : ∀ input outcome events, InScope input outcome events →
      ∃ kSrc, kSrc ≤ 459564194 ∧
        (evaluateTargetHOL s.machineConfig (sourceFfi input) (23077 + T kSrc)
          (s.initialState input)).1 ≠ .timeOut) :
    Certificate s (.finite (23077 + T 459564194)) := by
  apply certificate_finite_of_pipeline s 23077 459564194 T
  · intro a b h
    exact T_mono a b h
  · exact score
  · exact admitted
  · exact correct
  · exact transfer

end InitECandidate.Solver.Op3FiniteKBridge
