import InitECandidate.Runtime.SourceCostSharpCrepBasis
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCorrect
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! `pan_globals` expression transfer: under the original `pan_globals` state
relation, the compiled expression's canonical events cost no more than the
source expression's under `sharpScore`. A global read pays its `TopAddr`
load through its `globalAccess` event. -/

mutual
  /-- Expressions `pan_globals` compiles without a size change other than global
  reads: no `TopAddr` (rebased by `pan_globals`) and no named structs (removed
  by `pan_structs`). -/
  def globalsReadyExp : ExpHOL 64 → Bool
    | .topAddr | .nstruct _ _ | .nfield _ _ => false
    | .rstruct es | .op _ es | .panop _ es => globalsReadyExps es
    | .rfield _ e | .load _ e | .load32 e | .loadByte e => globalsReadyExp e
    | .cmp _ a b | .shift _ a b => globalsReadyExp a && globalsReadyExp b
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def globalsReadyExps : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => globalsReadyExp head && globalsReadyExps tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem globalsRel_targetStructs {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t) :
    t.structs = [] := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.2.2.2.2.2.2.1

theorem globalsRel_global {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    {name} {value : ValueHOL 64} (found : s.globals.lookup name = some value) :
    ∃ address, context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
      isWfShapeNilHOL (shapeOfHOLExact value) = true := by
  unfold panGlobalsStateRelHOLExact at rel
  obtain ⟨address, h1, h2, _⟩ := rel.2.2.2.2.2.2.2.2.1 name value found
  exact ⟨address, h1, h2⟩

theorem globals_value {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    {e : ExpHOL 64} {value : ValueHOL 64} (h : expressionValue s e = some value) :
    expressionValue t (compileExpExactHOL context e) = some value :=
  PanGlobalsCompileExpCorrect.compileExpCorrectHOL s e value context t ⟨rel, h⟩

theorem globals_resultWords {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    {e : ExpHOL 64} (ok : expressionValue s e ≠ none) :
    resultWords t (compileExpExactHOL context e) = resultWords s e := by
  rcases h : expressionValue s e with _ | value
  · exact absurd h ok
  · simp only [resultWords, h, globals_value rel h]

theorem globals_isWord {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    {e : ExpHOL 64} (ok : expressionValue s e ≠ none) :
    expressionIsWord t (compileExpExactHOL context e) = expressionIsWord s e := by
  rcases h : expressionValue s e with _ | value
  · exact absurd h ok
  · simp only [expressionIsWord, h, globals_value rel h]

theorem globals_compileList_length (context : PanGlobalsContextExact 64) :
    ∀ es : List (ExpHOL 64), (compileExpExactHOLList context es).length = es.length
  | [] => by simp [compileExpExactHOLList]
  | _ :: tail => by simp [compileExpExactHOLList, globals_compileList_length context tail]

theorem srcScore_statement (B : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.statement :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_statement, Nat.zero_add]

theorem srcScore_expression (B : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.expression :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_expression, Nat.zero_add]

theorem srcScore_copy (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.copy n :: rest) = 14 * n + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_copy]

theorem srcScore_frame (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.frame n :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_frame, Nat.zero_add]

theorem srcScore_scalar (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.scalar n :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_scalar, Nat.zero_add]

theorem srcScore_memory (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.memory n :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_memory, Nat.zero_add]

theorem srcScore_cost (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.cost n :: rest) = n + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_cost]

theorem srcScore_global (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.globalAccess n :: rest) = 176 + 166 * n + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_global]

theorem srcScore_expressionEvents (B : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    sharpSourceScore B (expressionEvents s e) = sourcePrice s e := by
  simp [expressionEvents, srcScore_cost, sharpSourceScore_nil]

/-- Normalise a sharp source score of an explicit event list. -/
macro "gsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [srcScore_statement, srcScore_cost, srcScore_copy, srcScore_frame,
    srcScore_scalar, srcScore_memory, srcScore_global, srcScore_expression, sharpSourceScore_append,
    sharpSourceScore_nil, List.cons_append, List.nil_append, List.append_assoc, statementUnit,
    whileOverhead, returnOverhead, raiseOverhead, callOverhead, slotOverhead, returnCopy,
    primitiveOverhead, storeOverhead] $[$loc]?)

/-- The `TopAddr`-relative global address costs its native price. -/
theorem globals_address_score {F : Type} (B : Nat) (t : PanSemStateFiniteExact 64 F) (address : BitVec 64) :
    sharpSourceScore B (expressionEvents t (.op .sub [.topAddr, .const address])) = globalAddressPrice srcK := by
  rw [srcScore_expressionEvents]
  simp [sourcePrice, sourcePrices, exprPrices, exprListPrices, cexpHeads, globalAddressPrice, srcK_top, srcK_cst, srcK_op]

theorem sharp_size_nil : ∀ shape : ShapeHOL,
    sizeOfShapeWithContextHOL [] shape = sizeOfShapeHOL shape := by
  refine ShapeHOL.rec
    (motive_1 := fun shape => sizeOfShapeWithContextHOL [] shape = sizeOfShapeHOL shape)
    (motive_2 := fun shapes => sizeOfShapesWithContextHOL [] shapes = sizeOfShapesHOL shapes)
    ?_ ?_ ?_ ?_ ?_
  · simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL]
  · intro shapes ih; simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL, ih]
  · intro name; simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL, structContextLookupHOL_nil]
  · simp [sizeOfShapesWithContextHOL, sizeOfShapesHOL]
  · intro head tail ihHead ihTail
    simp [sizeOfShapesWithContextHOL, sizeOfShapesHOL, ihHead, ihTail]

theorem sharp_value_some_load {F : Type} {s : PanSemStateFiniteExact 64 F} {shape : ShapeHOL}
    {address : ExpHOL 64} (ok : expressionValue s (.load shape address) ≠ none) :
    isWfShapeExactHOL s.structs shape = true ∧ ∃ w, expressionValue s address = some (.val (.word w)) := by
  simp only [expressionValue] at ok ⊢
  rw [evalHOLExact] at ok
  split at ok
  · rename_i wf
    refine ⟨wf, ?_⟩
    split at ok
    · rename_i a h; exact ⟨a, h⟩
    · exact absurd rfl ok
  · exact absurd rfl ok

theorem sharp_value_some_word_child {F : Type} {s : PanSemStateFiniteExact 64 F} {address : ExpHOL 64}
    {e : ExpHOL 64} (shape : e = .load32 address ∨ e = .loadByte address)
    (ok : expressionValue s e ≠ none) : ∃ w, expressionValue s address = some (.val (.word w)) := by
  rcases shape with rfl | rfl <;>
  · simp only [expressionValue] at ok ⊢
    rw [evalHOLExact] at ok
    split at ok
    · rename_i a h; exact ⟨a, h⟩
    · exact absurd rfl ok

theorem sharp_isWord {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} {w : BitVec 64}
    (h : expressionValue s e = some (.val (.word w))) : expressionIsWord s e = true := by
  simp [expressionIsWord, h]


#print axioms globals_address_score
end InitECandidate.Runtime.FineCost
