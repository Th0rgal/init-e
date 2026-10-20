import InitECandidate.Runtime.SourceCostSharpLowering
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
  /-- Address expressions whose every variable is read as a single word. -/
  def scalarAddr : ExpHOL 64 → Bool
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
    | .op _ args | .panop _ args => scalarAddrList args
    | .cmp _ left right | .shift _ left right => scalarAddr left && scalarAddr right
    | .load shape address => decide (sizeOfShapeHOL shape = 1) && scalarAddr address
    | .load32 address | .loadByte address => scalarAddr address
    | _ => false
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def scalarAddrList : List (ExpHOL 64) → Bool
    | [] => true
    | head :: tail => scalarAddr head && scalarAddrList tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Context-free sharp price of a scalar address expression. -/
  def sharpAddrPrice : ExpHOL 64 → Nat
    | .var .local _ => 6
    | .op _ args => 3 + sharpAddrListPrice args
    | .panop _ args => 4 + sharpAddrListPrice args
    | .cmp _ left right => 5 + sharpAddrPrice left + sharpAddrPrice right
    | .shift _ left right => 3 + sharpAddrPrice left + sharpAddrPrice right
    | .load _ address | .load32 address | .loadByte address => 3 + sharpAddrPrice address
    | .topAddr => 7
    | _ => 3
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def sharpAddrListPrice : List (ExpHOL 64) → Nat
    | [] => 0
    | head :: tail => sharpAddrPrice head + sharpAddrListPrice tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  /-- Site certificate: every multiword load has a scalar address whose
  context-free sharp price is at most `B`. -/
  def sharpSites (B : Nat) : ExpHOL 64 → Bool
    | .load shape address =>
        (decide (sizeOfShapeHOL shape ≤ 1) ||
          (scalarAddr address && decide (sharpAddrPrice address ≤ B))) && sharpSites B address
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

/-- A scalar address that evaluates to a word has sharp allowance at most its
context-free price. -/
theorem sharp_addr_bound {F : Type} (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64) :
    ∀ a : ExpHOL 64, scalarAddr a = true → LocalWidthsFitOn s context (varExpHOL a) →
      (∃ w, expressionValue s a = some (.val (.word w))) →
      panSharpAllowance context a ≤ sharpAddrPrice a := by
  refine ExpHOL.rec
    (motive_1 := fun a => scalarAddr a = true → LocalWidthsFitOn s context (varExpHOL a) →
      (∃ w, expressionValue s a = some (.val (.word w))) →
      panSharpAllowance context a ≤ sharpAddrPrice a)
    (motive_2 := fun args => scalarAddrList args = true →
      LocalWidthsFitOn s context ((args.map varExpHOL).flatten) →
      (∃ vs, @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args =
        some vs ∧ vs.all valueIsWord = true) →
      panSharpListAllowance context args ≤ sharpAddrListPrice args)
    (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro value _ _ _; simp [panSharpAllowance, sharpAddrPrice]
  · intro kind name _ layout word
    cases kind with
    | «local» =>
      simp only [panSharpAllowance, sharpAddrPrice]
      cases found : context.vars.lookup name with
      | none => simp
      | some data =>
        obtain ⟨shape, names⟩ := data
        obtain ⟨w, hw⟩ := word
        have fits := layout name (by simp [varExpHOL]) shape names found
        rw [sharp_resultWords_word s _ w hw] at fits
        simp only []
        omega
    | «global» => simp [panSharpAllowance, sharpAddrPrice]
  · intro fields _ supported; simp [scalarAddr] at supported
  · intro index value _ supported; simp [scalarAddr] at supported
  · intro name fields _ supported; simp [scalarAddr] at supported
  · intro name value _ supported; simp [scalarAddr] at supported
  · intro shape address ih supported layout word
    simp only [scalarAddr, Bool.and_eq_true, decide_eq_true_eq] at supported
    obtain ⟨w, hw⟩ := word
    have addressWord : ∃ a, expressionValue s address = some (.val (.word a)) := by
      simp only [expressionValue] at hw ⊢
      rw [evalHOLExact] at hw
      split at hw
      · split at hw
        · rename_i a h; exact ⟨a, h⟩
        · simp at hw
      · simp at hw
    have := ih supported.2 (by simpa [varExpHOL] using layout) addressWord
    simp only [panSharpAllowance, sharpAddrPrice, supported.1, Nat.sub_self, Nat.zero_mul]
    omega
  · intro address ih supported layout word
    simp only [scalarAddr] at supported
    obtain ⟨w, hw⟩ := word
    have addressWord : ∃ a, expressionValue s address = some (.val (.word a)) := by
      simp only [expressionValue] at hw ⊢
      rw [evalHOLExact] at hw
      split at hw
      · rename_i a h; exact ⟨a, h⟩
      · simp at hw
    have := ih supported (by simpa [varExpHOL] using layout) addressWord
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intro address ih supported layout word
    simp only [scalarAddr] at supported
    obtain ⟨w, hw⟩ := word
    have addressWord : ∃ a, expressionValue s address = some (.val (.word a)) := by
      simp only [expressionValue] at hw ⊢
      rw [evalHOLExact] at hw
      split at hw
      · rename_i a h; exact ⟨a, h⟩
      · simp at hw
    have := ih supported (by simpa [varExpHOL] using layout) addressWord
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intro operator args ih supported layout word
    simp only [scalarAddr] at supported
    obtain ⟨w, hw⟩ := word
    have argsWords : ∃ vs, @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args = some vs ∧ vs.all valueIsWord = true := by
      simp only [expressionValue] at hw
      rw [evalHOLExact] at hw
      split at hw
      · rename_i vs h
        split at hw
        · rename_i all; exact ⟨vs, h, all⟩
        · simp at hw
      · simp at hw
    have := ih supported (by simpa [varExpHOL] using layout) argsWords
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intro operator args ih supported layout word
    simp only [scalarAddr] at supported
    obtain ⟨w, hw⟩ := word
    have argsWords : ∃ vs, @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args = some vs ∧ vs.all valueIsWord = true := by
      simp only [expressionValue] at hw
      rw [evalHOLExact] at hw
      split at hw
      · rename_i vs h
        split at hw
        · rename_i all; exact ⟨vs, h, all⟩
        · simp at hw
      · simp at hw
    have := ih supported (by simpa [varExpHOL] using layout) argsWords
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intro operator left right ihLeft ihRight supported layout word
    simp only [scalarAddr, Bool.and_eq_true] at supported
    obtain ⟨w, hw⟩ := word
    have both : (∃ a, expressionValue s left = some (.val (.word a))) ∧
        (∃ b, expressionValue s right = some (.val (.word b))) := by
      simp only [expressionValue] at hw ⊢
      rw [evalHOLExact] at hw
      split at hw
      · rename_i a b ha hb; exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      · simp at hw
    simp only [varExpHOL] at layout
    have a := ihLeft supported.1 (fun n m => layout n (List.mem_append_left _ m)) both.1
    have b := ihRight supported.2 (fun n m => layout n (List.mem_append_right _ m)) both.2
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intro operator left right ihLeft ihRight supported layout word
    simp only [scalarAddr, Bool.and_eq_true] at supported
    obtain ⟨w, hw⟩ := word
    have both : (∃ a, expressionValue s left = some (.val (.word a))) ∧
        (∃ b, expressionValue s right = some (.val (.word b))) := by
      simp only [expressionValue] at hw ⊢
      rw [evalHOLExact] at hw
      split at hw
      · rename_i a b ha hb; exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      · simp at hw
    simp only [varExpHOL] at layout
    have a := ihLeft supported.1 (fun n m => layout n (List.mem_append_left _ m)) both.1
    have b := ihRight supported.2 (fun n m => layout n (List.mem_append_right _ m)) both.2
    simp only [panSharpAllowance, sharpAddrPrice]; omega
  · intros; simp [panSharpAllowance, sharpAddrPrice]
  · intros; simp [panSharpAllowance, sharpAddrPrice]
  · intros; simp [panSharpAllowance, sharpAddrPrice]
  · intros; simp [panSharpListAllowance, sharpAddrListPrice]
  · intro head tail ihHead ihTail supported layout words
    simp only [scalarAddrList, Bool.and_eq_true] at supported
    simp only [List.map_cons, List.flatten_cons] at layout
    obtain ⟨vs, hvs, all⟩ := words
    simp only [evalListHOLExact] at hvs
    split at hvs
    · rename_i v rest hv hrest
      simp only [Option.some.injEq] at hvs
      subst hvs
      simp only [List.all_cons, Bool.and_eq_true] at all
      have headWord : ∃ w, expressionValue s head = some (.val (.word w)) := by
        cases v with
        | val word => cases word with | word w => exact ⟨w, hv⟩
        | rStruct _ => simp [valueIsWord] at all
        | nStruct _ _ => simp [valueIsWord] at all
      have a := ihHead supported.1 (fun n m => layout n (List.mem_append_left _ m)) headWord
      have b := ihTail supported.2 (fun n m => layout n (List.mem_append_right _ m)) ⟨rest, hrest, all.2⟩
      simp only [panSharpListAllowance, sharpAddrListPrice]; omega
    · simp at hvs
  · trivial
  · intros; trivial
  · intros; trivial

#print axioms sharp_addr_bound

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
    have replay : (sizeOfShapeHOL shape - 1) * (panSharpAllowance context address + 5) ≤
        (B + 5) * (sizeOfShapeHOL shape - 1) := by
      rcases supported.1 with small | ⟨scalar, priced⟩
      · have : sizeOfShapeHOL shape - 1 = 0 := by omega
        rw [this]; simp
      · have addr := sharp_addr_bound s context address scalar
          (by simpa [varExpHOL] using layout) ⟨w, hw⟩
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
