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


end InitECandidate.Solver.HybridScoreBounds

namespace InitECandidate.Solver.HybridScoreBounds

/-- Tight source-clock bound for the worst block family. -/
def WORST_CASE_block : Nat := 459564194

theorem WORST_CASE_block_eq : WORST_CASE_block = 459564194 := rfl

/-- Every indexed loop has a positive, explicit component bound. -/
def WORST_CASE_loop (i : Nat) : Nat := WORST_CASE i

theorem WORST_CASE_loop_eq (i : Nat) : WORST_CASE_loop i = i + 1 := rfl

end InitECandidate.Solver.HybridScoreBounds
