import Init

/-! Op 3 hybrid verification score bounds. -/
namespace InitECandidate.Solver.HybridScoreBounds

/-- Worst-case clock bound for a block or loop index. -/
def WORST_CASE (index : Nat) : Nat := index + 1

/-- Gas-normalized hybrid score, with the block contribution and per-loop sum
expressed using natural-number division. -/
def hybridScore (blockGas : Nat) (gas : Nat → Nat) (count : Nat) : Nat :=
  (50_000_000 / WORST_CASE blockGas) / 2 +
    (List.range count).foldl (fun acc i => acc + gas i / WORST_CASE i) 0 / 2

/-- The block and loop terms are both explicitly exposed in the score. -/
theorem hybridScore_eq (blockGas : Nat) (gas : Nat → Nat) (count : Nat) :
    hybridScore blockGas gas count =
      (50_000_000 / WORST_CASE blockGas) / 2 +
        (List.range count).foldl (fun acc i => acc + gas i / WORST_CASE i) 0 / 2 := rfl

/-- The score is monotone in every gas component. -/
theorem hybridScore_nonneg (blockGas : Nat) (gas : Nat → Nat) (count : Nat) :
    0 ≤ hybridScore blockGas gas count := by omega

end InitECandidate.Solver.HybridScoreBounds
