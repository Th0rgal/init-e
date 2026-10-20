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

theorem compiled_load32_work_bound (context : PanToCrepContextExact 64)
    (address : ExpHOL 64) :
    flattenedExpressionWork context (.load32 address) ≤
      1 + flattenedExpressionWork context address := by
  unfold flattenedExpressionWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions <;> cases addressShape <;> simp [crepListWork, crepNodeWork] <;> omega

#print axioms compiled_load32_work_bound

theorem compiled_loadByte_work_bound (context : PanToCrepContextExact 64)
    (address : ExpHOL 64) :
    flattenedExpressionWork context (.loadByte address) ≤
      1 + flattenedExpressionWork context address := by
  unfold flattenedExpressionWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions <;> cases addressShape <;> simp [crepListWork, crepNodeWork] <;> omega

#print axioms compiled_loadByte_work_bound

theorem crepListWork_append (left right : List (CrepExpHOL 64)) :
    crepListWork (left ++ right) = crepListWork left + crepListWork right := by
  induction left with
  | nil => simp [crepListWork]
  | cons head tail ih => simp [crepListWork, ih, Nat.add_assoc]

/-- Record construction concatenates scalar fields without repeating them. -/
theorem compiled_record_work (context : PanToCrepContextExact 64)
    (fields : List (ExpHOL 64)) :
    flattenedExpressionWork context (.rstruct fields) =
      (fields.map (flattenedExpressionWork context)).sum := by
  unfold flattenedExpressionWork
  rw [compileExpExactHOLW]
  induction fields with
  | nil => simp [compileExpExactHOLWList, crepListWork]
  | cons head tail ih =>
    simp only [compileExpExactHOLWList, List.flatMap_cons, crepListWork_append,
      List.map_cons, List.sum_cons]
    rw [ih]

#print axioms compiled_record_work

theorem selected_heads_work_bound (arguments : List (List (CrepExpHOL 64)))
    (heads : List (CrepExpHOL 64)) (selected : cexpHeads arguments = some heads) :
    crepListWork heads ≤ (arguments.map crepListWork).sum := by
  induction arguments generalizing heads with
  | nil => simp [cexpHeads] at selected; subst heads; simp [crepListWork]
  | cons first rest ih =>
    cases first with
    | nil => simp [cexpHeads] at selected
    | cons head tail =>
      cases hc : cexpHeads rest with
      | none => simp [cexpHeads, hc] at selected
      | some chosen =>
        simp only [cexpHeads, hc, Option.some.injEq] at selected
        subst heads
        have smaller := ih chosen hc
        simp only [crepListWork, List.map_cons, List.sum_cons]
        omega

theorem compiled_arguments_work (context : PanToCrepContextExact 64)
    (arguments : List (ExpHOL 64)) :
    ((compileExpExactHOLWList context arguments).map
      (fun pair => crepListWork pair.1)).sum =
      (arguments.map (flattenedExpressionWork context)).sum := by
  induction arguments with
  | nil => simp [compileExpExactHOLWList]
  | cons head tail ih =>
    simp only [compileExpExactHOLWList, List.map_cons, List.sum_cons,
      flattenedExpressionWork, ih]


theorem compiled_op_work_bound (context : PanToCrepContextExact 64)
    (operator : BinOp) (arguments : List (ExpHOL 64)) :
    flattenedExpressionWork context (.op operator arguments) ≤
      1 + (arguments.map (flattenedExpressionWork context)).sum := by
  unfold flattenedExpressionWork
  rw [compileExpExactHOLW]
  cases hc : cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
  | none => simp [crepListWork, crepNodeWork]
  | some heads =>
    have bound := selected_heads_work_bound _ heads hc
    have total := compiled_arguments_work context arguments
    simp only [List.map_map, Function.comp_def] at bound
    simp only [crepListWork, crepNodeWork, Nat.add_zero]
    change crepListWork heads ≤ _ at bound
    rw [total] at bound
    exact Nat.add_le_add_left bound 1

#print axioms compiled_op_work_bound

theorem compiled_panop_work_bound (context : PanToCrepContextExact 64)
    (operator : PanOp) (arguments : List (ExpHOL 64)) :
    flattenedExpressionWork context (.panop operator arguments) ≤
      1 + (arguments.map (flattenedExpressionWork context)).sum := by
  unfold flattenedExpressionWork
  rw [compileExpExactHOLW]
  cases hc : cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
  | none => simp [crepListWork, crepNodeWork]
  | some heads =>
    have bound := selected_heads_work_bound _ heads hc
    have total := compiled_arguments_work context arguments
    simp only [List.map_map, Function.comp_def] at bound
    simp only [crepListWork, crepNodeWork, Nat.add_zero]
    change crepListWork heads ≤ _ at bound
    rw [total] at bound
    exact Nat.add_le_add_left bound 1

#print axioms compiled_panop_work_bound

theorem crepListWork_take_drop (expressions : List (CrepExpHOL 64)) (count : Nat) :
    crepListWork (expressions.take count) ≤ crepListWork expressions ∧
    crepListWork (expressions.drop count) ≤ crepListWork expressions := by
  have partition := congrArg crepListWork (List.take_append_drop count expressions)
  rw [crepListWork_append] at partition
  omega

/-- Field selection only discards scalar expressions. Invalid indices produce
one fallback constant, already covered by the additive unit. -/
theorem compField_work_bound (shapes : List ShapeHOL) (index : Nat)
    (expressions : List (CrepExpHOL 64)) :
    crepListWork (compFieldHOL index shapes expressions).1 ≤ 1 + crepListWork expressions := by
  induction shapes generalizing index expressions with
  | nil => simp [compFieldHOL, crepListWork, crepNodeWork]
  | cons shape shapes ih =>
    rw [compFieldHOL]
    split
    · exact Nat.le_trans (crepListWork_take_drop expressions (sizeOfShapeHOL shape)).1 (by omega)
    · have smaller := ih (index - 1) (expressions.drop (sizeOfShapeHOL shape))
      have discard := (crepListWork_take_drop expressions (sizeOfShapeHOL shape)).2
      omega

theorem compiled_field_work_bound (context : PanToCrepContextExact 64)
    (index : Nat) (record : ExpHOL 64) :
    flattenedExpressionWork context (.rfield index record) ≤
      1 + flattenedExpressionWork context record := by
  unfold flattenedExpressionWork
  generalize hc : compileExpExactHOLW context record = compiled
  obtain ⟨expressions, shape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases shape with
  | one => simp [crepListWork, crepNodeWork]
  | named name => simp [crepListWork, crepNodeWork]
  | comb shapes => exact compField_work_bound shapes index expressions

#print axioms compiled_field_work_bound

#print axioms compiled_load_work_bound
#print axioms loadShape_work_bound
end InitECandidate.Runtime.FineCost
