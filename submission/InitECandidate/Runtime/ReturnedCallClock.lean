import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime

/-- Call entry spends one tick; a checked body bound leaves the advertised
continuation budget in any returned body state. -/
theorem returned_call_tail_clock (clock remaining bodyCost tailCost : Nat)
    (budget : bodyCost + 1 + tailCost ≤ clock)
    (spent : clock - 1 ≤ remaining + bodyCost) : tailCost ≤ remaining := by
  omega

#print axioms returned_call_tail_clock
end InitECandidate.Runtime
