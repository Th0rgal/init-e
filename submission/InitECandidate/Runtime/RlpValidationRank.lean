import InitECandidate.Runtime.RlpValidationStackPop
namespace InitECandidate.Runtime
open Flapjack

/-- Pending interval work plus one unit for each future stack pop. -/
def rlpValidationPendingRank : List RlpValidationFrame → Nat
  | [] => 0
  | frame :: rest => 2 * (frame.stop.toNat - frame.resume.toNat) + 1 + rlpValidationPendingRank rest

/-- Two units per unread byte leave room to charge a subsequent stack pop. -/
def rlpValidationRank (position stop : BitVec 64) (frames : List RlpValidationFrame) : Nat :=
  2 * (stop.toNat - position.toNat) + rlpValidationPendingRank frames

/-- Advancing over a non-list item strictly decreases the validator measure. -/
theorem rlpValidation_rank_advance (position after stop : BitVec 64) (frames : List RlpValidationFrame)
    (advances : position.toNat < after.toNat) (bounded : after.toNat ≤ stop.toNat) :
    rlpValidationRank after stop frames < rlpValidationRank position stop frames := by
  unfold rlpValidationRank
  omega

/-- Entering a nested payload decreases the measure even after charging its
new continuation record, because the list header consumes at least one byte. -/
theorem rlpValidation_rank_push (position payload after stop record : BitVec 64)
    (frames : List RlpValidationFrame)
    (headerPositive : position.toNat < payload.toNat)
    (payloadOrdered : payload.toNat ≤ after.toNat) (bounded : after.toNat ≤ stop.toNat) :
    rlpValidationRank payload after ({record := record,resume := after,stop := stop} :: frames) <
      rlpValidationRank position stop frames := by
  simp only [rlpValidationRank,rlpValidationPendingRank]
  omega

/-- At the end of a payload, restoring its saved interval removes precisely
the one unit reserved for that pop. -/
theorem rlpValidation_rank_pop (position : BitVec 64) (frame : RlpValidationFrame)
    (frames : List RlpValidationFrame) :
    rlpValidationRank frame.resume frame.stop frames + 1 =
      rlpValidationRank position position (frame :: frames) := by
  simp only [rlpValidationRank,rlpValidationPendingRank,Nat.sub_self,Nat.mul_zero,Nat.zero_add]
  omega

/-- Initially there is no stack work, giving an explicit input-size bound. -/
theorem rlpValidation_rank_initial (pointer length : BitVec 64)
    (noWrap : pointer.toNat + length.toNat < 2^64) :
    rlpValidationRank pointer (pointer + length) [] = 2 * length.toNat := by
  simp only [rlpValidationRank,rlpValidationPendingRank,Nat.add_zero]
  rw [BitVec.toNat_add_of_lt noWrap]
  omega

#print axioms rlpValidation_rank_advance
#print axioms rlpValidation_rank_push
#print axioms rlpValidation_rank_pop
#print axioms rlpValidation_rank_initial
end InitECandidate.Runtime
