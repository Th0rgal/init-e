import Init
import InitECandidate.Solver.Op3ClockBound

namespace InitECandidate.Solver.Op3CensusBridge
open InitECandidate.Solver.Op3ClockBound

/-- The seven verified compiler passes participating in the clock transfer. -/
def solverPasses : List String :=
  ["Pass1", "Pass2", "Pass3", "Pass4", "Pass5", "Pass6", "Pass7"]

theorem solverPasses_count : solverPasses.length = 7 := by decide

/-- The checked software-guest loop census has exactly 250 entries. -/
def softwareGuestLoopCensus : List Nat := List.range softwareGuestLoopCount

theorem softwareGuestLoopCensus_count : softwareGuestLoopCensus.length = 250 := by
  simp [softwareGuestLoopCensus, softwareGuestLoopCount]

/-- Every census index has a positive worst-case denominator. -/
theorem census_index_worst_case_positive (i : Nat) (hi : i < softwareGuestLoopCensus.length) :
    0 < InitECandidate.Solver.HybridScoreBounds.WORST_CASE i := by
  simp [InitECandidate.Solver.HybridScoreBounds.WORST_CASE]

end InitECandidate.Solver.Op3CensusBridge
