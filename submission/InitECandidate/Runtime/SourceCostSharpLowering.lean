import InitECandidate.Runtime.SourceCostLoopPrice
import InitECandidate.Runtime.PanLoweringAllowance
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Sharp lowering of Pan expressions: the exact Loop price (`loopNodePrice`,
plus one move per element) of the Crep expressions `pan_to_crep` emits, and a
local allowance per source node that dominates it. -/

theorem sharpCrepList_nil : sharpCrepList [] = 0 := by simp [sharpCrepList, loopPriceList]

theorem sharpCrepList_cons (e : CrepExpHOL 64) (es : List (CrepExpHOL 64)) :
    sharpCrepList (e :: es) = loopNodePrice e + 1 + sharpCrepList es := by
  simp only [sharpCrepList, loopPriceList, List.length_cons]; omega

theorem loopPriceList_append (left right : List (CrepExpHOL 64)) :
    loopPriceList (left ++ right) = loopPriceList left + loopPriceList right := by
  induction left with
  | nil => simp [loopPriceList]
  | cons head tail ih => simp only [List.cons_append, loopPriceList, ih]; omega

theorem sharpCrepList_append (left right : List (CrepExpHOL 64)) :
    sharpCrepList (left ++ right) = sharpCrepList left + sharpCrepList right := by
  simp only [sharpCrepList, loopPriceList_append, List.length_append]; omega

theorem sharpCrepList_take_drop (expressions : List (CrepExpHOL 64)) (count : Nat) :
    sharpCrepList (expressions.take count) ≤ sharpCrepList expressions ∧
    sharpCrepList (expressions.drop count) ≤ sharpCrepList expressions := by
  have partition := congrArg sharpCrepList (List.take_append_drop count expressions)
  rw [sharpCrepList_append] at partition
  omega

/-- A `k`-word structured load replays its address once per word, with an
offset addition for every word after the first. -/
theorem loadShape_sharp_bound (offset : BitVec 64) (words : Nat) (address : CrepExpHOL 64) :
    sharpCrepList (loadShapeBytesHOLW offset words address) ≤
      words * (loopNodePrice address + 6) := by
  induction words generalizing offset with
  | zero => simp [loadShapeBytesHOLW, sharpCrepList_nil]
  | succ words ih =>
    simp only [loadShapeBytesHOLW, sharpCrepList_cons]
    have tail := ih (offset + BitVec.ofNat 64 (64 / 8))
    split <;> simp only [loopNodePrice, loopPriceList] <;> rw [Nat.succ_mul] <;> omega

/-- The first word of a structured load reads the address itself; every
further word adds an offset. -/
theorem loadShape_sharp_first (words : Nat) (address : CrepExpHOL 64) :
    sharpCrepList (loadShapeBytesHOLW 0 words address) ≤
      loopNodePrice address + 2 + (words - 1) * (loopNodePrice address + 6) := by
  cases words with
  | zero => simp [loadShapeBytesHOLW, sharpCrepList_nil]
  | succ words =>
    simp only [loadShapeBytesHOLW, sharpCrepList_cons]
    have tail := loadShape_sharp_bound (0 + BitVec.ofNat 64 (64 / 8)) words address
    simp only [beq_self_eq_true, if_true, loopNodePrice, Nat.add_sub_cancel]
    omega

/-- Exact Loop price of the head of a compiled expression list: the only
part a structured load re-evaluates for each further word. -/
def crepHead : List (CrepExpHOL 64) → Nat
  | [] => 0
  | head :: _ => loopNodePrice head

/-- Sharp Crep price of a compiled Pan expression. -/
def flattenedSharpWork (context : PanToCrepContextExact 64) (e : ExpHOL 64) : Nat :=
  sharpCrepList (compileExpExactHOLW context e).1

theorem sharp_selected_heads (arguments : List (List (CrepExpHOL 64)))
    (heads : List (CrepExpHOL 64)) (selected : cexpHeads arguments = some heads) :
    loopPriceList heads + heads.length ≤ (arguments.map sharpCrepList).sum := by
  induction arguments generalizing heads with
  | nil => simp [cexpHeads] at selected; subst heads; simp [loopPriceList]
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
        have own : loopNodePrice head + 1 ≤ sharpCrepList (head :: tail) := by
          rw [sharpCrepList_cons]; omega
        simp only [loopPriceList, List.map_cons, List.sum_cons, List.length_cons]
        omega

theorem sharp_compiled_arguments (context : PanToCrepContextExact 64) (arguments : List (ExpHOL 64)) :
    ((compileExpExactHOLWList context arguments).map (fun pair => sharpCrepList pair.1)).sum =
      (arguments.map (flattenedSharpWork context)).sum := by
  induction arguments with
  | nil => simp [compileExpExactHOLWList]
  | cons head tail ih =>
    simp only [compileExpExactHOLWList, List.map_cons, List.sum_cons, flattenedSharpWork, ih]

theorem sharp_compiled_op (context : PanToCrepContextExact 64) (operator : BinOp)
    (arguments : List (ExpHOL 64)) :
    flattenedSharpWork context (.op operator arguments) ≤
      3 + (arguments.map (flattenedSharpWork context)).sum := by
  rw [flattenedSharpWork]
  rw [compileExpExactHOLW]
  cases hc : cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
  | none => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | some heads =>
    have bound := sharp_selected_heads _ heads hc
    have total := sharp_compiled_arguments context arguments
    simp only [List.map_map, Function.comp_def] at bound
    rw [total] at bound
    simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons, List.length_nil]
    omega

theorem sharp_compiled_panop (context : PanToCrepContextExact 64) (operator : PanOp)
    (arguments : List (ExpHOL 64)) :
    flattenedSharpWork context (.panop operator arguments) ≤
      4 + (arguments.map (flattenedSharpWork context)).sum := by
  rw [flattenedSharpWork]
  rw [compileExpExactHOLW]
  cases hc : cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
  | none => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | some heads =>
    have bound := sharp_selected_heads _ heads hc
    have total := sharp_compiled_arguments context arguments
    simp only [List.map_map, Function.comp_def] at bound
    rw [total] at bound
    simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons, List.length_nil]
    omega

theorem sharp_head_le (head : CrepExpHOL 64) (tail : List (CrepExpHOL 64)) :
    loopNodePrice head + 1 ≤ sharpCrepList (head :: tail) := by
  rw [sharpCrepList_cons]; omega

theorem sharp_compiled_cmp (context : PanToCrepContextExact 64) (operator : Cmp) (left right : ExpHOL 64) :
    flattenedSharpWork context (.cmp operator left right) ≤
      5 + flattenedSharpWork context left + flattenedSharpWork context right := by
  unfold flattenedSharpWork
  generalize hl : compileExpExactHOLW context left = compiledLeft
  generalize hr : compileExpExactHOLW context right = compiledRight
  obtain ⟨lefts, leftShape⟩ := compiledLeft
  obtain ⟨rights, rightShape⟩ := compiledRight
  rw [compileExpExactHOLW, hl, hr]
  cases lefts with
  | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | cons a as =>
    cases rights with
    | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
    | cons b bs =>
      have ha := sharp_head_le a as
      have hb := sharp_head_le b bs
      simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons, List.length_nil] at ha hb ⊢
      omega

theorem sharp_compiled_shift (context : PanToCrepContextExact 64) (operator : Shift) (left right : ExpHOL 64) :
    flattenedSharpWork context (.shift operator left right) ≤
      3 + flattenedSharpWork context left + flattenedSharpWork context right := by
  unfold flattenedSharpWork
  generalize hl : compileExpExactHOLW context left = compiledLeft
  generalize hr : compileExpExactHOLW context right = compiledRight
  obtain ⟨lefts, leftShape⟩ := compiledLeft
  obtain ⟨rights, rightShape⟩ := compiledRight
  rw [compileExpExactHOLW, hl, hr]
  cases lefts with
  | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | cons a as =>
    cases rights with
    | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
    | cons b bs =>
      have ha := sharp_head_le a as
      have hb := sharp_head_le b bs
      simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons, List.length_nil] at ha hb ⊢
      omega

theorem sharp_compiled_load32 (context : PanToCrepContextExact 64) (address : ExpHOL 64) :
    flattenedSharpWork context (.load32 address) ≤ 3 + flattenedSharpWork context address := by
  unfold flattenedSharpWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions with
  | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | cons a as =>
    have ha := sharp_head_le a as
    cases addressShape <;> simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons,
      List.length_nil] at ha ⊢ <;> omega

theorem sharp_compiled_loadByte (context : PanToCrepContextExact 64) (address : ExpHOL 64) :
    flattenedSharpWork context (.loadByte address) ≤ 3 + flattenedSharpWork context address := by
  unfold flattenedSharpWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions with
  | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | cons a as =>
    have ha := sharp_head_le a as
    cases addressShape <;> simp only [sharpCrepList, loopPriceList, loopNodePrice, List.length_cons,
      List.length_nil] at ha ⊢ <;> omega

theorem sharp_compiled_load (context : PanToCrepContextExact 64) (shape : ShapeHOL) (address : ExpHOL 64) :
    flattenedSharpWork context (.load shape address) ≤
      3 + flattenedSharpWork context address +
        (sizeOfShapeHOL shape - 1) * (crepHead (compileExpExactHOLW context address).1 + 6) := by
  unfold flattenedSharpWork
  generalize hc : compileExpExactHOLW context address = compiled
  obtain ⟨expressions, addressShape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases expressions with
  | nil => (simp [sharpCrepList, loopPriceList, loopNodePrice]) <;> omega
  | cons head tail =>
    have localBound := loadShape_sharp_first (sizeOfShapeHOL shape) head
    have hh := sharp_head_le head tail
    simp only [crepHead]
    omega

theorem sharp_compField (shapes : List ShapeHOL) (index : Nat) (expressions : List (CrepExpHOL 64)) :
    sharpCrepList (compFieldHOL index shapes expressions).1 ≤ 3 + sharpCrepList expressions := by
  induction shapes generalizing index expressions with
  | nil => simp [compFieldHOL, sharpCrepList, loopPriceList, loopNodePrice]
  | cons shape shapes ih =>
    rw [compFieldHOL]
    split
    · exact Nat.le_trans (sharpCrepList_take_drop expressions (sizeOfShapeHOL shape)).1 (by omega)
    · have smaller := ih (index - 1) (expressions.drop (sizeOfShapeHOL shape))
      have discard := (sharpCrepList_take_drop expressions (sizeOfShapeHOL shape)).2
      omega

theorem sharp_compiled_field (context : PanToCrepContextExact 64) (index : Nat) (record : ExpHOL 64) :
    flattenedSharpWork context (.rfield index record) ≤ 3 + flattenedSharpWork context record := by
  unfold flattenedSharpWork
  generalize hc : compileExpExactHOLW context record = compiled
  obtain ⟨expressions, shape⟩ := compiled
  rw [compileExpExactHOLW, hc]
  cases shape with
  | one => simp [sharpCrepList, loopPriceList, loopNodePrice]
  | named name => simp [sharpCrepList, loopPriceList, loopNodePrice]
  | comb shapes => exact sharp_compField shapes index expressions

theorem sharp_compiled_record (context : PanToCrepContextExact 64) (fields : List (ExpHOL 64)) :
    flattenedSharpWork context (.rstruct fields) = (fields.map (flattenedSharpWork context)).sum := by
  unfold flattenedSharpWork
  rw [compileExpExactHOLW]
  induction fields with
  | nil => simp [compileExpExactHOLWList, sharpCrepList_nil]
  | cons head tail ih =>
    simp only [compileExpExactHOLWList, List.flatMap_cons, sharpCrepList_append,
      List.map_cons, List.sum_cons]
    rw [ih]

theorem sharp_variables (names : List Nat) :
    sharpCrepList (names.map (CrepExpHOL.var (width := 64))) = 3 * names.length := by
  induction names with
  | nil => simp [sharpCrepList_nil]
  | cons head tail ih =>
    simp only [List.map_cons, sharpCrepList_cons, ih, loopNodePrice, List.length_cons]; omega

mutual
  /-- Local sharp allowance of one Pan expression, mirroring `pan_to_crep`. -/
  def panSharpAllowance (context : PanToCrepContextExact 64) : ExpHOL 64 → Nat
    | .var .local name =>
        match context.vars.lookup name with
        | some (_, names) => 3 * names.length
        | none => 3
    | .rstruct fields => panSharpListAllowance context fields
    | .rfield _ value => 3 + panSharpAllowance context value
    | .load shape address => 3 + panSharpAllowance context address +
        (sizeOfShapeHOL shape - 1) * (crepHead (compileExpExactHOLW context address).1 + 6)
    | .load32 address | .loadByte address => 3 + panSharpAllowance context address
    | .op _ args => 3 + panSharpListAllowance context args
    | .panop _ args => 4 + panSharpListAllowance context args
    | .cmp _ left right => 5 + panSharpAllowance context left + panSharpAllowance context right
    | .shift _ left right => 3 + panSharpAllowance context left + panSharpAllowance context right
    | .topAddr => 7
    | _ => 3
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def panSharpListAllowance (context : PanToCrepContextExact 64) : List (ExpHOL 64) → Nat
    | [] => 0
    | head :: tail => panSharpAllowance context head + panSharpListAllowance context tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem sharp_lowering_bound (context : PanToCrepContextExact 64) :
    ∀ e : ExpHOL 64, flattenedSharpWork context e ≤ panSharpAllowance context e := by
  refine ExpHOL.rec
    (motive_1 := fun e => flattenedSharpWork context e ≤ panSharpAllowance context e)
    (motive_2 := fun es => (es.map (flattenedSharpWork context)).sum ≤ panSharpListAllowance context es)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value
    simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · intro kind name
    cases kind with
    | «local» =>
      cases hv : context.vars.lookup name with
      | none =>
        simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, hv, sharpCrepList,
          loopPriceList, loopNodePrice]
      | some data =>
        obtain ⟨shape, names⟩ := data
        have := sharp_variables names
        simp only [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, hv]
        exact Nat.le_of_eq this
    | «global» =>
      simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
        loopNodePrice]
  · intro fields ih
    simp only [panSharpAllowance]
    rw [sharp_compiled_record]
    exact ih
  · intro index value ih
    simp only [panSharpAllowance]
    exact Nat.le_trans (sharp_compiled_field context index value) (Nat.add_le_add_left ih 3)
  · intro name fields ih
    simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · intro name value ih
    simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · intro shape address ih
    simp only [panSharpAllowance]
    have := sharp_compiled_load context shape address
    omega
  · intro address ih
    simp only [panSharpAllowance]
    exact Nat.le_trans (sharp_compiled_load32 context address) (Nat.add_le_add_left ih 3)
  · intro address ih
    simp only [panSharpAllowance]
    exact Nat.le_trans (sharp_compiled_loadByte context address) (Nat.add_le_add_left ih 3)
  · intro operator args ih
    simp only [panSharpAllowance]
    exact Nat.le_trans (sharp_compiled_op context operator args) (Nat.add_le_add_left ih 3)
  · intro operator args ih
    simp only [panSharpAllowance]
    exact Nat.le_trans (sharp_compiled_panop context operator args) (Nat.add_le_add_left ih 4)
  · intro operator left right ihLeft ihRight
    simp only [panSharpAllowance]
    have bound := sharp_compiled_cmp context operator left right
    omega
  · intro operator left right ihLeft ihRight
    simp only [panSharpAllowance]
    have bound := sharp_compiled_shift context operator left right
    omega
  · simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · simp [flattenedSharpWork, compileExpExactHOLW, panSharpAllowance, sharpCrepList, loopPriceList,
      loopNodePrice]
  · simp [panSharpListAllowance]
  · intro head tail ihHead ihTail
    simp only [List.map_cons, List.sum_cons, panSharpListAllowance]
    omega
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms sharp_lowering_bound
end InitECandidate.Runtime.FineCost
