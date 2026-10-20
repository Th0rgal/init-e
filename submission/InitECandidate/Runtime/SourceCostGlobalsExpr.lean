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
    sharpSourceScore B (.statement :: rest) = 10 + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_statement]

theorem srcScore_expression (B : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.expression :: rest) = 5 + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_expression]

theorem srcScore_copy (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.copy n :: rest) = 5 * n + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_copy]

theorem srcScore_frame (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.frame n :: rest) = 4 * n + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_frame]

theorem srcScore_scalar (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.scalar n :: rest) = sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_scalar, Nat.zero_add]

theorem srcScore_memory (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.memory n :: rest) = 12 * n + (B + 5) * (n - 1) + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_memory]

theorem srcScore_global (B n : Nat) (rest : List WorkEvent) :
    sharpSourceScore B (.globalAccess n :: rest) =
      40 + 17 * n + (B + 5) * (n - 1) + sharpSourceScore B rest := by
  simp only [sharpSourceScore_cons, sharpSource_global]

/-- The `TopAddr`-relative global address costs 25 under the sharp score. -/
theorem globals_address_score {F : Type} (B : Nat) (t : PanSemStateFiniteExact 64 F) (address : BitVec 64) :
    sharpSourceScore B (expressionEvents t (.op .sub [.topAddr, .const address])) = 25 := by
  rw [expressionEvents]
  simp only [expressionListEvents]
  rw [expressionEvents, expressionEvents]
  simp only [List.cons_append, List.nil_append, List.append_nil, srcScore_expression,
    srcScore_copy, srcScore_scalar, sharpSourceScore_nil, List.length_cons, List.length_nil]

#print axioms globals_address_score
end InitECandidate.Runtime.FineCost
