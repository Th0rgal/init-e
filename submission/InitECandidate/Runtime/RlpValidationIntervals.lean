import InitECandidate.Runtime.RlpValidationRank
namespace InitECandidate.Runtime
open Flapjack

/-- The active interval is ordered and every saved resume point lies beyond
its nested interval, so pending input intervals do not overlap. -/
inductive RlpValidationIntervals : BitVec 64 → BitVec 64 → List RlpValidationFrame → Prop where
  | nil (position stop : BitVec 64) (ordered : position.toNat ≤ stop.toNat) :
      RlpValidationIntervals position stop []
  | cons (position stop : BitVec 64) (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
      (ordered : position.toNat ≤ stop.toNat)
      (nested : stop.toNat ≤ frame.resume.toNat)
      (tail : RlpValidationIntervals frame.resume frame.stop rest) :
      RlpValidationIntervals position stop (frame :: rest)

def rlpValidationOuterStop (stop : BitVec 64) : List RlpValidationFrame → BitVec 64
  | [] => stop
  | frame :: rest => rlpValidationOuterStop frame.stop rest

/-- Moving within the current interval retains all pending interval ordering. -/
theorem RlpValidationIntervals.reposition {position stop after : BitVec 64} {frames : List RlpValidationFrame}
    (valid : RlpValidationIntervals position stop frames) (bounded : after.toNat ≤ stop.toNat) :
    RlpValidationIntervals after stop frames := by
  cases valid with
  | nil => exact .nil after stop bounded
  | cons _ _ frame rest _ nested tail => exact .cons after stop frame rest bounded nested tail

/-- Entering a nested payload saves an ordered continuation interval. -/
theorem RlpValidationIntervals.push {position stop payload after record : BitVec 64} {frames : List RlpValidationFrame}
    (valid : RlpValidationIntervals position stop frames)
    (payloadOrdered : payload.toNat ≤ after.toNat) (bounded : after.toNat ≤ stop.toNat) :
    RlpValidationIntervals payload after ({record := record,resume := after,stop := stop} :: frames) := by
  exact .cons payload after _ frames payloadOrdered (Nat.le_refl _) (valid.reposition bounded)

/-- Popping a finished nested interval restores its ordered saved interval. -/
theorem RlpValidationIntervals.pop {position stop : BitVec 64} {frame : RlpValidationFrame} {frames : List RlpValidationFrame}
    (valid : RlpValidationIntervals position stop (frame :: frames)) :
    RlpValidationIntervals frame.resume frame.stop frames := by
  cases valid with | cons _ _ _ _ _ _ tail => exact tail

/-- Disjoint ordered pending intervals bound all remaining rank by the outer
input span plus one unit per saved continuation. -/
theorem RlpValidationIntervals.rank_bound {position stop : BitVec 64} {frames : List RlpValidationFrame}
    (valid : RlpValidationIntervals position stop frames) :
    position.toNat ≤ (rlpValidationOuterStop stop frames).toNat ∧
      rlpValidationRank position stop frames ≤
        2 * ((rlpValidationOuterStop stop frames).toNat - position.toNat) + frames.length := by
  induction valid with
  | nil position stop ordered =>
    simp only [rlpValidationOuterStop,rlpValidationRank,rlpValidationPendingRank,List.length_nil,Nat.add_zero]
    exact ⟨ordered,Nat.le_refl _⟩
  | cons position stop frame rest ordered nested tail ih =>
    simp only [rlpValidationOuterStop,rlpValidationRank,rlpValidationPendingRank,List.length_cons]
    dsimp only [rlpValidationRank] at ih
    exact ⟨by omega,by omega⟩

/-- A non-wrapping input interval starts ordered with no pending intervals
and exactly twice its byte length as validation rank. -/
theorem rlpValidation_intervals_initial (pointer length : BitVec 64)
    (noWrap : pointer.toNat + length.toNat < 2^64) :
    RlpValidationIntervals pointer (pointer + length) [] ∧
      rlpValidationRank pointer (pointer + length) [] = 2 * length.toNat := by
  refine ⟨.nil pointer (pointer + length) ?_,rlpValidation_rank_initial pointer length noWrap⟩
  rw [BitVec.toNat_add_of_lt noWrap]
  omega

#print axioms rlpValidation_intervals_initial
#print axioms RlpValidationIntervals.reposition
#print axioms RlpValidationIntervals.push
#print axioms RlpValidationIntervals.pop
#print axioms RlpValidationIntervals.rank_bound
end InitECandidate.Runtime
