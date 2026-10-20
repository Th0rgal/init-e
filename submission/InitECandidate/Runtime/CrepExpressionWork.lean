import Flapjack.Pancake.PanToCrep.CompileExact
namespace InitECandidate.Runtime.FineCost
open Flapjack

mutual
  /-- Scalar expression-node work after structure flattening. Constants have
  unit cost regardless of their numeric value. Variable-arity children are
  counted individually. Native expansion coefficients are a separate proof. -/
  def crepNodeWork : CrepExpHOL 64 → Nat
    | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => 1
    | .load e | .load32 e | .loadByte e => 1 + crepNodeWork e
    | .op _ args | .crepOp _ args => 1 + crepListWork args
    | .cmp _ left right | .shift _ left right =>
        1 + crepNodeWork left + crepNodeWork right
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def crepListWork : List (CrepExpHOL 64) → Nat
    | [] => 0
    | head :: tail => crepNodeWork head + crepListWork tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Structure loads duplicate address evaluation once per flattened word.
Each expansion adds at most a load, an offset addition and an offset constant.
This is a local bound, independent of the enclosing program size. -/
theorem loadShape_work_bound (offset : BitVec 64) (words : Nat) (address : CrepExpHOL 64) :
    crepListWork (loadShapeBytesHOLW offset words address) ≤
      words * (crepNodeWork address + 3) := by
  induction words generalizing offset with
  | zero => simp [loadShapeBytesHOLW, crepListWork]
  | succ words ih =>
    simp only [loadShapeBytesHOLW, crepListWork]
    split <;> simp only [crepNodeWork, crepListWork]
    all_goals
      have tail := ih (offset + BitVec.ofNat 64 (64 / 8))
      rw [Nat.succ_mul]
      omega

#print axioms loadShape_work_bound
end InitECandidate.Runtime.FineCost
