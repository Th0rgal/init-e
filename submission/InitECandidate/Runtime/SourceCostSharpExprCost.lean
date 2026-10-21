import InitECandidate.Runtime.SourceCostSharpHead
import InitECandidate.Runtime.PanScopedCostTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! The sharp lowering allowance of a source expression is paid by the
expression's own canonical events: five per expression node, three per copied
word, and, for each multiword load, `(B + 5)` per memory word beyond the
first, where `B` certifies the scalar address price at that load site. -/

/-- Memory words beyond the first of each memory event: the number of address
replays a structured load or store performs. -/
def replayUnits : List WorkEvent → Nat
  | [] => 0
  | .memory k :: rest => (k - 1) + replayUnits rest
  | .globalAccess k :: rest => (k - 1) + replayUnits rest
  | _ :: rest => replayUnits rest

/-- Expression weights of the sharp source score. -/
def sharpExprWeights : Work := { expressions := 5, movedWords := 3 }

/-- Sharp expression score: expression and copy events plus the certified
replay allowance. -/
def sharpExprScore (B : Nat) (ev : List WorkEvent) : Nat :=
  sharpExprWeights.score (executionWork ev) + (B + 5) * replayUnits ev

theorem replayUnits_append (a b : List WorkEvent) :
    replayUnits (a ++ b) = replayUnits a + replayUnits b := by
  induction a with
  | nil => simp [replayUnits]
  | cons head tail ih =>
    cases head <;> simp only [List.cons_append, replayUnits, ih] <;> omega

theorem sharpExprScore_nil (B : Nat) : sharpExprScore B [] = 0 := by
  simp [sharpExprScore, replayUnits, executionWork, Work.score]

theorem sharpExprScore_append (B : Nat) (a b : List WorkEvent) :
    sharpExprScore B (a ++ b) = sharpExprScore B a + sharpExprScore B b := by
  simp only [sharpExprScore, executionWork_score_append, replayUnits_append, Nat.mul_add]; omega

theorem sharpExprScore_cons (B : Nat) (event : WorkEvent) (rest : List WorkEvent) :
    sharpExprScore B (event :: rest) =
      sharpExprWeights.score event.units + (B + 5) * replayUnits [event] + sharpExprScore B rest := by
  have := sharpExprScore_append B [event] rest
  simp only [List.singleton_append] at this
  rw [this]
  simp only [sharpExprScore, executionWork, Work.score_plus]
  have : executionWork [] = ({} : Work) := rfl
  simp [Work.score, replayUnits]

@[simp] theorem sharp_units_expression (B : Nat) :
    sharpExprWeights.score WorkEvent.expression.units + (B + 5) * replayUnits [.expression] = 5 := by
  simp [sharpExprWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharp_units_copy (B n : Nat) :
    sharpExprWeights.score (WorkEvent.copy n).units + (B + 5) * replayUnits [.copy n] = 3 * n := by
  simp [sharpExprWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharp_units_scalar (B n : Nat) :
    sharpExprWeights.score (WorkEvent.scalar n).units + (B + 5) * replayUnits [.scalar n] = 0 := by
  simp [sharpExprWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharp_units_memory (B n : Nat) :
    sharpExprWeights.score (WorkEvent.memory n).units + (B + 5) * replayUnits [.memory n] =
      (B + 5) * (n - 1) := by
  simp [sharpExprWeights, Work.score, WorkEvent.units, replayUnits]

mutual
  /-- Site certificate: every multiword load has a grammar address whose
  context-free head price, plus one, is at most `B`. -/
  def sharpSites (B : Nat) : ExpHOL 64 → Bool
    | .load shape address =>
        (decide (sizeOfShapeHOL shape ≤ 1) ||
          (headAddr address && decide (sharpHeadPrice address + 1 ≤ B))) && sharpSites B address
    | .rstruct es | .op _ es | .panop _ es => sharpSitesList B es
    | .rfield _ e | .load32 e | .loadByte e => sharpSites B e
    | .cmp _ a b | .shift _ a b => sharpSites B a && sharpSites B b
    | _ => true
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def sharpSitesList (B : Nat) : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => sharpSites B head && sharpSitesList B tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem sharp_resultWords_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (w : BitVec 64)
    (h : expressionValue s e = some (.val (.word w))) : resultWords s e = 1 := by
  simp [resultWords, h, flattenHOL]


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

/-- The sharp lowering allowance of a successfully evaluated source expression
is paid by its own canonical events under the site certificate. -/
theorem sharp_expression_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (B : Nat) (structs : s.structs = []) :
    ∀ e : ExpHOL 64, LocalWidthsFitOn s context (varExpHOL e) → sharpSites B e = true →
      expressionValue s e ≠ none →
      panSharpAllowance context e ≤ sharpExprScore B (expressionEvents s e) := by
  refine ExpHOL.rec
    (motive_1 := fun e => LocalWidthsFitOn s context (varExpHOL e) → sharpSites B e = true →
      expressionValue s e ≠ none →
      panSharpAllowance context e ≤ sharpExprScore B (expressionEvents s e))
    (motive_2 := fun es => LocalWidthsFitOn s context ((es.map varExpHOL).flatten) →
      sharpSitesList B es = true →
      @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es ≠ none →
      panSharpListAllowance context es ≤ sharpExprScore B (expressionListEvents s es))
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _ _ _
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_expression, sharp_units_copy,
      panSharpAllowance]
    omega
  · intro kind name layout _ _
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_expression, sharp_units_copy]
    cases kind with
    | «local» =>
      simp only [panSharpAllowance]
      cases found : context.vars.lookup name with
      | none => simp only []; omega
      | some data =>
        obtain ⟨shape, names⟩ := data
        have fits := layout name (by simp [varExpHOL]) shape names found
        simp only []
        omega
    | «global» => simp only [panSharpAllowance]; omega
  · intro fields ih layout supported ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) fields ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]; rfl
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported) children
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      sharp_units_copy, panSharpAllowance]
    omega
  · intro index value ih layout supported ok
    have child : expressionValue s value ≠ none := by
      intro h; apply ok; simp only [expressionValue] at h ⊢; rw [evalHOLExact, h]
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported) child
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      sharp_units_copy, panSharpAllowance]
    omega
  · intro name fields _ _ _ _
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharp_units_expression, panSharpAllowance]
    omega
  · intro name value _ _ _ _
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharp_units_expression, panSharpAllowance]
    omega
  · intro shape address ih layout supported ok
    obtain ⟨wf, w, hw⟩ := sharp_value_some_load ok
    simp only [sharpSites, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at supported
    have smaller := ih (by simpa [varExpHOL] using layout) supported.2 (by rw [hw]; simp)
    have size : sizeOfShapeWithContextHOL s.structs shape = sizeOfShapeHOL shape := by
      rw [structs]; exact sharp_size_nil shape
    have replay : (sizeOfShapeHOL shape - 1) * (crepHead (compileExpExactHOLW context address).1 + 6) ≤
        (B + 5) * (sizeOfShapeHOL shape - 1) := by
      rcases supported.1 with small | ⟨grammar, priced⟩
      · have : sizeOfShapeHOL shape - 1 = 0 := by omega
        rw [this]; simp
      · have addr := head_bound context address grammar
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (by omega)
    rw [expressionEvents]
    simp only [wf, sharp_isWord hw, ↓reduceIte, size, sharpExprScore_cons, sharpExprScore_append,
      sharpExprScore_nil, sharp_units_expression, sharp_units_copy, sharp_units_memory,
      panSharpAllowance]
    omega
  · intro address ih layout supported ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inl rfl) ok
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported)
      (by rw [hw]; simp)
    rw [expressionEvents]
    simp only [sharp_isWord hw, ↓reduceIte, sharpExprScore_cons, sharpExprScore_append,
      sharpExprScore_nil, sharp_units_expression, sharp_units_copy, sharp_units_memory,
      panSharpAllowance]
    omega
  · intro address ih layout supported ok
    obtain ⟨w, hw⟩ := sharp_value_some_word_child (Or.inr rfl) ok
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported)
      (by rw [hw]; simp)
    rw [expressionEvents]
    simp only [sharp_isWord hw, ↓reduceIte, sharpExprScore_cons, sharpExprScore_append,
      sharpExprScore_nil, sharp_units_expression, sharp_units_copy, sharp_units_memory,
      panSharpAllowance]
    omega
  · intro operator args ih layout supported ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported) children
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      sharp_units_scalar, panSharpAllowance]
    omega
  · intro operator args ih layout supported ok
    have children : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args ≠ none := by
      intro h; apply ok; simp only [expressionValue]; rw [evalHOLExact, h]
    have smaller := ih (by simpa [varExpHOL] using layout) (by simpa [sharpSites] using supported) children
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      sharp_units_scalar, panSharpAllowance]
    omega
  · intro operator left right ihLeft ihRight layout supported ok
    simp only [sharpSites, Bool.and_eq_true] at supported
    simp only [varExpHOL] at layout
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    have a := ihLeft (fun n m => layout n (List.mem_append_left _ m)) supported.1 both.1
    have b := ihRight (fun n m => layout n (List.mem_append_right _ m)) supported.2 both.2
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      panSharpAllowance]
    split <;> simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_scalar] <;> omega
  · intro operator left right ihLeft ihRight layout supported ok
    simp only [sharpSites, Bool.and_eq_true] at supported
    simp only [varExpHOL] at layout
    have both : expressionValue s left ≠ none ∧ expressionValue s right ≠ none := by
      constructor <;> intro h <;> apply ok <;> simp only [expressionValue] at h ⊢ <;>
        rw [evalHOLExact] <;> simp [h]
    have a := ihLeft (fun n m => layout n (List.mem_append_left _ m)) supported.1 both.1
    have b := ihRight (fun n m => layout n (List.mem_append_right _ m)) supported.2 both.2
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_append, sharpExprScore_nil, sharp_units_expression,
      panSharpAllowance]
    split <;> simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_scalar] <;> omega
  · intros
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_expression, sharp_units_copy,
      panSharpAllowance]
    omega
  · intros
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_expression, sharp_units_copy,
      panSharpAllowance]
    omega
  · intros
    rw [expressionEvents]
    simp only [sharpExprScore_cons, sharpExprScore_nil, sharp_units_expression, sharp_units_copy,
      panSharpAllowance]
    omega
  · intros
    simp [panSharpListAllowance, expressionListEvents, sharpExprScore_nil]
  · intro head tail ihHead ihTail layout supported ok
    simp only [sharpSitesList, Bool.and_eq_true] at supported
    simp only [List.map_cons, List.flatten_cons] at layout
    have both : expressionValue s head ≠ none ∧ @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) tail ≠ none := by
      simp only [evalListHOLExact] at ok
      constructor
      · intro h; apply ok; simp only [expressionValue] at h; simp [h]
      · intro h; apply ok; simp [h]
    have a := ihHead (fun n m => layout n (List.mem_append_left _ m)) supported.1 both.1
    have b := ihTail (fun n m => layout n (List.mem_append_right _ m)) supported.2 both.2
    rw [expressionListEvents, sharpExprScore_append]
    simp only [panSharpListAllowance]
    omega
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms sharp_expression_bound

#print axioms sharpExprScore_append
end InitECandidate.Runtime.FineCost
