import InitECandidate.Runtime.SourceCostCrepBasis
import InitECandidate.Runtime.PanSourcePriceState
import InitECandidate.Runtime.SourceCostLoopPricing
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Sharp Pan-to-Crep pricing: source events are scored at native Crep prices
and pay Crep work at exact Loop prices (`CrepWorkS`). Expression events carry
their exact native price (`sourcePrice`) and statements their native Crep
overheads (`cost` events); a moved word costs 14, a stored word 142 (the store
unit, its address and value variables, and the offset of every word after the
first) and a shared-memory operation 37. `.statement` only counts. -/

/-! Price lists of compiled expression lists. -/

theorem sharpCrepList_nil : sharpCrepList [] = 0 := by simp [sharpCrepList, loopPriceList]

theorem sharpCrepList_cons (e : CrepExpHOL 64) (es : List (CrepExpHOL 64)) :
    sharpCrepList (e :: es) = loopNodePrice e + 39 + sharpCrepList es := by
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

theorem loopPriceList_nil' : loopPriceList [] = 0 := by simp [loopPriceList]

theorem loopPriceList_cons' (e : CrepExpHOL 64) (es : List (CrepExpHOL 64)) :
    loopPriceList (e :: es) = loopNodePrice e + loopPriceList es := by
  simp only [loopPriceList]

theorem loopPriceList_take_drop (expressions : List (CrepExpHOL 64)) (count : Nat) :
    loopPriceList (expressions.take count) ≤ loopPriceList expressions ∧
    loopPriceList (expressions.drop count) ≤ loopPriceList expressions := by
  have partition := congrArg loopPriceList (List.take_append_drop count expressions)
  rw [loopPriceList_append] at partition
  omega

theorem cexpHeads_length' {α : Type} : ∀ (ces : List (List α)) (hs : List α),
    cexpHeads ces = some hs → hs.length = ces.length
  | [], hs, h => by simp [cexpHeads] at h; subst h; rfl
  | c :: cs, hs, h => by
    simp only [cexpHeads] at h
    split at h
    · cases h
    · cases h
    · rename_i x _ rest hr
      simp only [Option.some.injEq] at h
      subst h
      simp [cexpHeads_length' cs rest hr]

theorem compileList_length' (context : PanToCrepContextExact 64) (es : List (ExpHOL 64)) :
    (compileExpExactHOLWList context es).length = es.length := by
  induction es with
  | nil => simp [compileExpExactHOLWList]
  | cons e es ih => simp [compileExpExactHOLWList, ih]


/-- Sharp source weights. -/
def sharpSourceWeights : Work :=
  { movedWords := 14, memoryAccesses := 142, nativeEvents := 37, nativeCost := 1,
    globalAccesses := 128, globalWords := 156 }

/-- Sharp source score of an event list. The certificate argument is kept for
the callers' interface; exact expression prices need no replay certificate. -/
def sharpSourceScore (_B : Nat) (ev : List WorkEvent) : Nat :=
  sharpSourceWeights.score (executionWork ev)

theorem sharpSourceScore_nil (B : Nat) : sharpSourceScore B [] = 0 := by
  simp [sharpSourceScore, executionWork, Work.score]

theorem sharpSourceScore_append (B : Nat) (a b : List WorkEvent) :
    sharpSourceScore B (a ++ b) = sharpSourceScore B a + sharpSourceScore B b := by
  simp only [sharpSourceScore, executionWork_score_append]

theorem sharpSourceScore_cons (B : Nat) (event : WorkEvent) (rest : List WorkEvent) :
    sharpSourceScore B (event :: rest) =
      sharpSourceWeights.score event.units + sharpSourceScore B rest := by
  simp only [sharpSourceScore, executionWork_score_cons]

@[simp] theorem sharpSource_statement : sharpSourceWeights.score WorkEvent.statement.units = 0 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_expression : sharpSourceWeights.score WorkEvent.expression.units = 0 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_copy (n : Nat) : sharpSourceWeights.score (WorkEvent.copy n).units = 14 * n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_frame (n : Nat) : sharpSourceWeights.score (WorkEvent.frame n).units = 0 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_scalar (n : Nat) : sharpSourceWeights.score (WorkEvent.scalar n).units = 0 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_memory (n : Nat) :
    sharpSourceWeights.score (WorkEvent.memory n).units = 142 * n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_native : sharpSourceWeights.score WorkEvent.nativeEvent.units = 37 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

@[simp] theorem sharpSource_cost (n : Nat) : sharpSourceWeights.score (WorkEvent.cost n).units = n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

/-- A global destination access pays its `pan_globals` expansion: the
`TopAddr`-relative address and the stores of its words. -/
@[simp] theorem sharpSource_global (n : Nat) :
    sharpSourceWeights.score (WorkEvent.globalAccess n).units = 128 + 156 * n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units]

/-- Static site condition on an expression. Exact expression prices need no
replay certificate, so every site qualifies. -/
def sharpSites (_B : Nat) (_e : ExpHOL 64) : Bool := true

def sharpSitesList (_B : Nat) (_es : List (ExpHOL 64)) : Bool := true

/-- Static site certificate over programs: every executed expression position
satisfies `sharpSites B`. -/
def sharpSitesProg (B : Nat) : ProgHOL 64 → Bool
  | .dec _ _ e body => sharpSites B e && sharpSitesProg B body
  | .assign _ _ e | .return e | .raise _ e => sharpSites B e
  | .primitive _ _ es => sharpSitesList B es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => sharpSites B a && sharpSites B b
  | .seq a b => sharpSitesProg B a && sharpSitesProg B b
  | .ite e a b => sharpSites B e && sharpSitesProg B a && sharpSitesProg B b
  | .while e body => sharpSites B e && sharpSitesProg B body
  | .call (some (_, some (_, _, handler))) _ es => sharpSitesList B es && sharpSitesProg B handler
  | .call _ _ es => sharpSitesList B es
  | .decCall _ _ _ es body => sharpSitesList B es && sharpSitesProg B body
  | .extCall _ a b c d => sharpSites B a && sharpSites B b && sharpSites B c && sharpSites B d
  | .shMemLoad _ _ _ e => sharpSites B e
  | _ => true
termination_by p => sizeOf p

/-- The certificate argument of the sharp statement transfer. -/
def sharpReplayBound : Nat := 0

/-- Sharp source score. -/
abbrev sharpScore (ev : List WorkEvent) : Nat := sharpSourceScore sharpReplayBound ev

theorem sharpScore_nil : sharpScore [] = 0 := sharpSourceScore_nil _

theorem sharpScore_append (a b : List WorkEvent) :
    sharpScore (a ++ b) = sharpScore a + sharpScore b := sharpSourceScore_append _ a b

theorem sharpScore_statement (rest : List WorkEvent) :
    sharpScore (.statement :: rest) = sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_statement, Nat.zero_add]

theorem sharpScore_expression (rest : List WorkEvent) :
    sharpScore (.expression :: rest) = sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_expression, Nat.zero_add]

theorem sharpScore_copy (n : Nat) (rest : List WorkEvent) :
    sharpScore (.copy n :: rest) = 14 * n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_copy]

theorem sharpScore_frame (n : Nat) (rest : List WorkEvent) :
    sharpScore (.frame n :: rest) = sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_frame, Nat.zero_add]

theorem sharpScore_scalar (n : Nat) (rest : List WorkEvent) :
    sharpScore (.scalar n :: rest) = sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_scalar, Nat.zero_add]

theorem sharpScore_memory (n : Nat) (rest : List WorkEvent) :
    sharpScore (.memory n :: rest) = 142 * n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_memory]

theorem sharpScore_cost (n : Nat) (rest : List WorkEvent) :
    sharpScore (.cost n :: rest) = n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_cost]

theorem sharpScore_native (rest : List WorkEvent) :
    sharpScore (.nativeEvent :: rest) = 37 + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_native]

theorem sharpScore_global (n : Nat) (rest : List WorkEvent) :
    sharpScore (.globalAccess n :: rest) = 128 + 156 * n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_global]

/-- An expression's events score its native price. -/
theorem sharpScore_expressionEvents {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    sharpScore (expressionEvents s e) = sourcePrice s e := by
  simp [expressionEvents, sharpScore_cost, sharpScore_nil]

/-- Compiled expression work at exact Loop prices is paid by the source
expression's own event: the price is exact. -/
theorem compiled_expression_sharp_score {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (localised : localisedExpHOL expression = true) :
    loopPriceList (compileExpExactHOLW context expression).1 = sharpScore (expressionEvents s expression) := by
  rw [sharpScore_expressionEvents]
  exact sourcePrice_compile s context targetLocals related expression value evaluated localised

#print axioms compiled_expression_sharp_score
end InitECandidate.Runtime.FineCost
