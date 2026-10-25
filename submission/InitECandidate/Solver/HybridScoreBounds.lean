import Init
namespace InitECandidate.Solver.HybridScoreBounds

def WORST_CASE (index : Nat) : Nat := index + 1

def loopSum (gas : Nat → Nat) (count : Nat) : Nat :=
  (List.range count).foldl (fun acc i => acc + gas i / WORST_CASE i) 0

/-- Twice the hybrid score, avoiding fractional notation in the kernel. -/
def hybridScore2 (blockGas : Nat) (gas : Nat → Nat) (count : Nat) : Nat :=
  50_000_000 / WORST_CASE blockGas + loopSum gas count

theorem hybridScore2_eq (blockGas : Nat) (gas : Nat → Nat) (count : Nat) :
    hybridScore2 blockGas gas count =
      50_000_000 / WORST_CASE blockGas +
        (List.range count).foldl (fun acc i => acc + gas i / WORST_CASE i) 0 := rfl

theorem worst_case_positive (i : Nat) : 0 < WORST_CASE i := by simp [WORST_CASE]

theorem hybridScore2_nonneg (blockGas : Nat) (gas : Nat → Nat) (count : Nat) :
    0 ≤ hybridScore2 blockGas gas count := by omega

end InitECandidate.Solver.HybridScoreBounds
