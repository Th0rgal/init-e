import InitECandidate.Runtime.CrepExpressionWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

mutual
  /-- A local source-expression allowance for the Pan-to-Crep pass. Sizes of
  variable values and structured loads are explicit; literal magnitude is free.
  Named structures/globals use this pass's fallback because their preprocessing
  passes must be certified separately before applying this theorem. -/
  def panLoweringAllowance (context : PanToCrepContextExact 64) : ExpHOL 64 → Nat
    | .var .local name =>
        match context.vars.lookup name with
        | some (_, names) => names.length
        | none => 1
    | .rstruct fields => panLoweringListAllowance context fields
    | .rfield _ value => 1 + panLoweringAllowance context value
    | .load shape address =>
        1 + sizeOfShapeHOL shape * (panLoweringAllowance context address + 3)
    | .load32 address | .loadByte address => 1 + panLoweringAllowance context address
    | .op _ args | .panop _ args => 1 + panLoweringListAllowance context args
    | .cmp _ left right | .shift _ left right =>
        1 + panLoweringAllowance context left + panLoweringAllowance context right
    | _ => 1
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panLoweringListAllowance (context : PanToCrepContextExact 64) : List (ExpHOL 64) → Nat
    | [] => 0
    | head :: tail => panLoweringAllowance context head + panLoweringListAllowance context tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem crep_variables_work (names : List Nat) :
    crepListWork (names.map (CrepExpHOL.var (width := 64))) = names.length := by
  induction names with
  | nil => simp [crepListWork]
  | cons head tail ih => simp [crepListWork, crepNodeWork, ih, Nat.add_comm]

/-- All exact expression constructors are covered at this compiler pass.
This is a local expansion theorem, not an end-to-end runtime certificate. -/
theorem pan_lowering_work_bound (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, flattenedExpressionWork context e ≤ panLoweringAllowance context e := by
  refine ExpHOL.rec
    (motive_1 := fun e => flattenedExpressionWork context e ≤ panLoweringAllowance context e)
    (motive_2 := fun es => (es.map (flattenedExpressionWork context)).sum ≤ panLoweringListAllowance context es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value
    simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · intro kind name
    cases kind with
    | «local» =>
      simp only [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance]
      split <;> simp_all [crep_variables_work, crepListWork, crepNodeWork]
    | «global» =>
      simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · intro fields ih
    simp only [panLoweringAllowance]
    rw [compiled_record_work]
    exact ih
  · intro index value ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_field_work_bound context index value) (Nat.add_le_add_left ih 1)
  · intro name fields ih
    simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · intro name value ih
    simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · intro shape address ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_load_work_bound context shape address)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right ih 3)) 1)
  · intro address ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_load32_work_bound context address) (Nat.add_le_add_left ih 1)
  · intro address ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_loadByte_work_bound context address) (Nat.add_le_add_left ih 1)
  · intro operator args ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_op_work_bound context operator args) (Nat.add_le_add_left ih 1)
  · intro operator args ih
    simp only [panLoweringAllowance]
    exact Nat.le_trans (compiled_panop_work_bound context operator args) (Nat.add_le_add_left ih 1)
  · intro operator left right ihLeft ihRight
    simp only [panLoweringAllowance]
    have bound := compiled_cmp_work_bound context operator left right
    change _ ≤ 1 + panLoweringAllowance context left + panLoweringAllowance context right
    omega
  · intro operator left right ihLeft ihRight
    simp only [panLoweringAllowance]
    have bound := compiled_shift_work_bound context operator left right
    change _ ≤ 1 + panLoweringAllowance context left + panLoweringAllowance context right
    omega
  · simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · simp [flattenedExpressionWork, compileExpExactHOLW, panLoweringAllowance, crepListWork, crepNodeWork]
  · simp [panLoweringListAllowance]
  · intro head tail ihHead ihTail
    simp only [List.map_cons, List.sum_cons, panLoweringListAllowance]
    omega
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms pan_lowering_work_bound
end InitECandidate.Runtime.FineCost
