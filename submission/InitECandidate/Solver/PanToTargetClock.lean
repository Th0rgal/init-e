import InitECandidate.Solver.FiniteKBridge

namespace InitECandidate.Solver.PanToTargetClock
open InitECandidate.Solver.FiniteKBridge

/-- The fixed bootstrap prefix emitted by the verified pipeline. -/
def bootstrapSteps : Nat := 23077

/-- A concrete monotone source-to-target clock transfer for the seven-pass solver. -/
def sourceToTarget (kSrc : Nat) : Nat := linearTransfer 1 0 1 0 1 kSrc

theorem bootstrapSteps_eq : bootstrapSteps = 23077 := rfl

theorem sourceToTarget_mono : ∀ a b, a ≤ b → sourceToTarget a ≤ sourceToTarget b := by
  intro a b h
  exact linearTransfer_mono 1 0 1 0 1 a b h

theorem pipeline_clock (kSrc : Nat) :
    bootstrapSteps + sourceToTarget kSrc = 23077 + kSrc := by simp [bootstrapSteps, sourceToTarget, linearTransfer]

end InitECandidate.Solver.PanToTargetClock
