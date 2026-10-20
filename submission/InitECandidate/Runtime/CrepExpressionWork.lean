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

open Flapjack.Pancake.PanLang

/-- Compiler-aware local expression allowance. Unlike a whole-program syntax
maximum, it is evaluated for the expression whose execution is being charged. -/
def flattenedExpressionWork (context : PanToCrepContextExact 64) (e : ExpHOL 64) : Nat :=
  crepListWork (compileExpExactHOLW context e).1

/-- The actual source load clause has a size-dependent expansion bound. The
extra unit covers the compiler's empty-address fallback, including zero shapes. -/
theorem compiled_load_work_bound (context : PanToCrepContextExact 64)
    (shape : ShapeHOL) (address : ExpHOL 64) :
    flattenedExpressionWork context (.load shape address) ≤
      1 + sizeOfShapeHOL shape * (flattenedExpressionWork context address + 3) := by
  unfold flattenedExpressionWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions with
  | nil => simp [crepListWork, crepNodeWork]
  | cons head tail =>
    have localBound := loadShape_work_bound (0#64) (sizeOfShapeHOL shape) head
    have larger := Nat.mul_le_mul_left (sizeOfShapeHOL shape)
      (show crepNodeWork head + 3 ≤ crepListWork (head :: tail) + 3 by
        simp only [crepListWork]; omega)
    exact Nat.le_trans localBound (by simpa using Nat.le_trans larger (Nat.le_add_left _ 1))

/-- Scalar cmp lowering adds one node to the selected operand expressions. -/
theorem compiled_cmp_work_bound (context : PanToCrepContextExact 64)
    (operator : Cmp) (left right : ExpHOL 64) :
    flattenedExpressionWork context (.cmp operator left right) ≤
      1 + flattenedExpressionWork context left + flattenedExpressionWork context right := by
  unfold flattenedExpressionWork
  generalize hl : compileExpExactHOLW context left = compiledLeft
  generalize hr : compileExpExactHOLW context right = compiledRight
  obtain ⟨lefts, leftShape⟩ := compiledLeft
  obtain ⟨rights, rightShape⟩ := compiledRight
  rw [compileExpExactHOLW, hl, hr]
  cases lefts <;> cases rights <;> simp [crepListWork, crepNodeWork] <;> omega

#print axioms compiled_cmp_work_bound

/-- Scalar shift lowering adds one node to the selected operand expressions. -/
theorem compiled_shift_work_bound (context : PanToCrepContextExact 64)
    (operator : Shift) (left right : ExpHOL 64) :
    flattenedExpressionWork context (.shift operator left right) ≤
      1 + flattenedExpressionWork context left + flattenedExpressionWork context right := by
  unfold flattenedExpressionWork
  generalize hl : compileExpExactHOLW context left = compiledLeft
  generalize hr : compileExpExactHOLW context right = compiledRight
  obtain ⟨lefts, leftShape⟩ := compiledLeft
  obtain ⟨rights, rightShape⟩ := compiledRight
  rw [compileExpExactHOLW, hl, hr]
  cases lefts <;> cases rights <;> simp [crepListWork, crepNodeWork] <;> omega

#print axioms compiled_shift_work_bound

#print axioms compiled_load_work_bound
#print axioms loadShape_work_bound
end InitECandidate.Runtime.FineCost
