import InitECandidate.Runtime.DecodeStepScratchCapacity
namespace InitECandidate.Runtime

/-- An empty stack has no unwind work; a nonempty stack gets smaller when
unwinding to an older record at a higher address. -/
def decodeWitnessStackDistance (top : BitVec 64) : Nat :=
  if top = 0 then 0 else 2^64 - top.toNat

def decodeWitnessMeasureLayer : Nat := 100 * 2^64 + 100

/-- Arithmetic measure for the explicit-stack machine. The caller must establish
its physical-record invariant and mode transitions from actual source runs.
A fresh push decreases capacity; pops increase record addresses; branch delivery
uses one child credit. Mode credits are resolve=3, decode=2, deliver=1, done=0. -/
def decodeWitnessMeasure (capacity : Nat) (top : BitVec 64) (children mode : Nat) : Nat :=
  capacity * decodeWitnessMeasureLayer + 100 * decodeWitnessStackDistance top + 5 * children + mode

theorem decodeWitnessStackDistance_bound (top : BitVec 64) :
    decodeWitnessStackDistance top ≤ 2^64 := by
  unfold decodeWitnessStackDistance
  split <;> omega

theorem decodeWitnessMeasure_bound (capacity : Nat) (top : BitVec 64) (children mode : Nat)
    (childBound : children ≤ 16) (modeBound : mode ≤ 3) :
    decodeWitnessMeasure capacity top children mode < (capacity + 1) * decodeWitnessMeasureLayer := by
  have distance := decodeWitnessStackDistance_bound top
  unfold decodeWitnessMeasure decodeWitnessMeasureLayer
  omega

/-- One real scratch-record push dominates every possible change in the
remaining frame, child and mode components. -/
theorem decodeWitnessMeasure_push (capacity nextCapacity : Nat) (top nextTop : BitVec 64)
    (children nextChildren mode nextMode : Nat) (progress : nextCapacity < capacity)
    (childBound : nextChildren ≤ 16) (modeBound : nextMode ≤ 3) :
    decodeWitnessMeasure nextCapacity nextTop nextChildren nextMode < decodeWitnessMeasure capacity top children mode := by
  have nextBound := decodeWitnessMeasure_bound nextCapacity nextTop nextChildren nextMode childBound modeBound
  have layers : (nextCapacity + 1) * decodeWitnessMeasureLayer ≤ capacity * decodeWitnessMeasureLayer :=
    Nat.mul_le_mul_right _ (by omega)
  unfold decodeWitnessMeasure at *
  omega

/-- Popping an actual record to its enclosing higher-address record, or to the
empty stack, dominates a reset of the current-frame child and mode credits. -/
theorem decodeWitnessMeasure_pop (capacity : Nat) (top nextTop : BitVec 64)
    (children nextChildren mode nextMode : Nat) (nonempty : top ≠ 0)
    (older : nextTop = 0 ∨ top.toNat < nextTop.toNat)
    (childBound : nextChildren ≤ 16) (modeBound : nextMode ≤ 3) :
    decodeWitnessMeasure capacity nextTop nextChildren nextMode < decodeWitnessMeasure capacity top children mode := by
  have topBound := top.isLt
  have nextBound := nextTop.isLt
  unfold decodeWitnessMeasure decodeWitnessStackDistance
  rw [if_neg nonempty]
  by_cases empty : nextTop = 0
  · rw [if_pos empty]
    omega
  · rw [if_neg empty]
    have larger : top.toNat < nextTop.toNat := older.resolve_left empty
    omega

/-- Consuming a branch child credit pays for the transition from delivery back
to resolution without allocating another frame. -/
theorem decodeWitnessMeasure_child (capacity : Nat) (top : BitVec 64)
    (children nextChildren mode nextMode : Nat) (progress : nextChildren < children)
    (modeBound : nextMode ≤ 3) :
    decodeWitnessMeasure capacity top nextChildren nextMode < decodeWitnessMeasure capacity top children mode := by
  unfold decodeWitnessMeasure
  omega

theorem decodeWitnessMeasure_mode (capacity : Nat) (top : BitVec 64)
    (children mode nextMode : Nat) (progress : nextMode < mode) :
    decodeWitnessMeasure capacity top children nextMode < decodeWitnessMeasure capacity top children mode := by
  unfold decodeWitnessMeasure
  omega

#print axioms decodeWitnessMeasure_bound
#print axioms decodeWitnessMeasure_push
#print axioms decodeWitnessMeasure_pop
#print axioms decodeWitnessMeasure_child
#print axioms decodeWitnessMeasure_mode
end InitECandidate.Runtime
