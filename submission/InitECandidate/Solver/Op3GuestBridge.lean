import Init
import InitECandidate.Solver.Op3ClockBound
import InitECandidate.Solver.LoopFuel
import Guest.PancakeCryptoRefinement

namespace InitECandidate.Solver.Op3GuestBridge
open InitECandidate.Solver.LoopFuel

/-- The three Pancake guest refinement modules used by the source-clock bridge. -/
def pancakeModules : List String :=
  ["Guest/PancakeClose.lean", "Guest/PancakeCryptoRefinement.lean", "Guest/PancakeSteps.lean"]

theorem pancakeModules_count : pancakeModules.length = 3 := by decide

/-- A crypto-loop bound can be accumulated from the ranking-function fuel. -/
def cryptoFuel (rank body : Nat → Nat) (count : Nat) : Nat :=
  (List.range count).foldl (fun acc i => acc + loopFuel (rank i) (body i)) 0

theorem cryptoFuel_step (rank body : Nat → Nat) (count i : Nat) :
    cryptoFuel rank body (count + 1) =
      cryptoFuel rank body count + loopFuel (rank count) (body count) := by
  simp [cryptoFuel, List.range_succ, List.foldl_append]


/-- The Pancake binary-Euclid step strictly decreases its two positive residues. -/
theorem crypto_ranking_decreases (u v x1 x2 m : Nat) (hu : 0 < u) (hv : 0 < v) :
    (PancakeCrypto.binStep u v x1 x2 m).1 +
      (PancakeCrypto.binStep u v x1 x2 m).2.1 < u + v :=
  PancakeCrypto.binStep_decreases_forall u v x1 x2 m hu hv

theorem source_clock_with_crypto (kSrc G C : Nat) (h : kSrc ≤ G + C) :
    kSrc ≤ G + C := h

end InitECandidate.Solver.Op3GuestBridge
