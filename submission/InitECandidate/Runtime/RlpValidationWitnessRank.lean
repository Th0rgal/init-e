import InitECandidate.Runtime.RlpValidationLoopInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- One extra unit charges the final iteration that clears the loop flag. -/
def RlpValidationLoopWitness.rank {F : Type} {state : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {ceiling inputLimit : Nat}
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) : Nat :=
  rlpValidationRank valid.position valid.stop valid.frames + 1

/-- Entering a while body spends clock but retains every invariant field. -/
def RlpValidationLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {ceiling inputLimit : Nat}
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) :
    RlpValidationLoopWitness (decClockHOLFinite state) frame ceiling inputLimit :=
  { valid with }

@[simp] theorem RlpValidationLoopWitness.decClock_rank {F : Type} {state : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {ceiling inputLimit : Nat}
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) : valid.decClock.rank = valid.rank := rfl

/-- A least-rank witness gives a state-based measure without assuming uniqueness
of ghost stack certificates; any produced successor bounds the next minimum. -/
theorem rlpValidation_exists_minimal_witness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64) (ceiling inputLimit : Nat)
    (inhabited : Nonempty (RlpValidationLoopWitness state frame ceiling inputLimit)) :
    ∃ valid : RlpValidationLoopWitness state frame ceiling inputLimit,
      ∀ other : RlpValidationLoopWitness state frame ceiling inputLimit, valid.rank ≤ other.rank := by
  classical
  have existsRank : ∃ n : Nat, ∃ valid : RlpValidationLoopWitness state frame ceiling inputLimit, valid.rank = n := by
    obtain ⟨valid⟩ := inhabited
    exact ⟨valid.rank,valid,rfl⟩
  obtain ⟨valid,equal⟩ := Nat.find_spec existsRank
  refine ⟨valid,?_⟩
  intro other
  rw [equal]
  exact Nat.find_min' existsRank ⟨other,rfl⟩

/-- The enabled-loop measure is positive and bounded by twice the input limit
plus the one final flag-clearing iteration. -/
theorem RlpValidationLoopWitness.rank_bound {F : Type} {state : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {ceiling inputLimit : Nat}
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) :
    0 < valid.rank ∧ valid.rank ≤ 2 * inputLimit + 1 := by
  have bounded := valid.rankBound
  unfold RlpValidationLoopWitness.rank
  omega

#print axioms rlpValidation_exists_minimal_witness
#print axioms RlpValidationLoopWitness.rank_bound
end InitECandidate.Runtime
