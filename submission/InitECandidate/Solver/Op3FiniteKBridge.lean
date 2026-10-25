import InitECandidate.Solver.FiniteKBridge
import InitECandidate.Solver.Op3ClockBound
import InitECandidate.Solver.Op3CensusBridge
import InitECandidate.Solver.Op3GuestBridge
import InitECandidate.Solver.HybridScoreBounds

namespace InitECandidate.Solver.Op3FiniteKBridge
open InitECandidate.Solver.FiniteKBridge
open InitECandidate.Solver.Op3ClockBound

/-- Fixed bootstrap prefix supplied by the verified initialisation trace. -/
def bootstrapSteps : Nat := 23077

/-- The explicit monotone transfer used by the finite-K certificate. -/
def T (kSrc : Nat) : Nat := linearTransfer 1 0 1 0 1 kSrc

theorem bootstrapSteps_exact : bootstrapSteps = 23077 := rfl

theorem T_mono : ∀ a b, a ≤ b → T a ≤ T b := by
  intro a b h
  exact linearTransfer_mono 1 0 1 0 1 a b h

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
