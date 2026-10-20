import InitECandidate.Runtime.SourceCostCrepBasis
import InitECandidate.Runtime.SourceCostSharpExprCost
import InitECandidate.Runtime.SourceCostLoopPricing
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Sharp Pan-to-Crep pricing: source events are scored by a sharp weight
vector plus the certified load-address replay allowance, and pay Crep work at
exact Loop prices (`CrepWorkS`). -/

/-- Sharp source weights. Expression and copy weights pay exact expression
lowering (`sharp_expression_bound`); statement, memory and frame weights pay
the Crep statements emitted per executed statement, stored word and frame slot. -/
def sharpSourceWeights : Work :=
  { statements := 10, expressions := 5, movedWords := 5, memoryAccesses := 12, frameSlots := 4,
    globalAccesses := 40, globalWords := 17 }

/-- Sharp source score of an event list with replay certificate `B`. -/
def sharpSourceScore (B : Nat) (ev : List WorkEvent) : Nat :=
  sharpSourceWeights.score (executionWork ev) + (B + 5) * replayUnits ev

theorem sharpSourceScore_nil (B : Nat) : sharpSourceScore B [] = 0 := by
  simp [sharpSourceScore, replayUnits, executionWork, Work.score]

theorem sharpSourceScore_append (B : Nat) (a b : List WorkEvent) :
    sharpSourceScore B (a ++ b) = sharpSourceScore B a + sharpSourceScore B b := by
  simp only [sharpSourceScore, executionWork_score_append, replayUnits_append, Nat.mul_add]; omega

theorem sharpSourceScore_cons (B : Nat) (event : WorkEvent) (rest : List WorkEvent) :
    sharpSourceScore B (event :: rest) =
      sharpSourceWeights.score event.units + (B + 5) * replayUnits [event] +
        sharpSourceScore B rest := by
  have := sharpSourceScore_append B [event] rest
  simp only [List.singleton_append] at this
  rw [this]
  simp only [sharpSourceScore, executionWork, Work.score_plus]
  simp [Work.score, replayUnits]

@[simp] theorem sharpSource_statement (B : Nat) :
    sharpSourceWeights.score WorkEvent.statement.units + (B + 5) * replayUnits [.statement] = 10 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharpSource_expression (B : Nat) :
    sharpSourceWeights.score WorkEvent.expression.units + (B + 5) * replayUnits [.expression] = 5 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharpSource_copy (B n : Nat) :
    sharpSourceWeights.score (WorkEvent.copy n).units + (B + 5) * replayUnits [.copy n] = 5 * n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharpSource_frame (B n : Nat) :
    sharpSourceWeights.score (WorkEvent.frame n).units + (B + 5) * replayUnits [.frame n] = 4 * n := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharpSource_scalar (B n : Nat) :
    sharpSourceWeights.score (WorkEvent.scalar n).units + (B + 5) * replayUnits [.scalar n] = 0 := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

@[simp] theorem sharpSource_memory (B n : Nat) :
    sharpSourceWeights.score (WorkEvent.memory n).units + (B + 5) * replayUnits [.memory n] =
      12 * n + (B + 5) * (n - 1) := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

/-- A global access pays its `pan_globals` expansion: the `TopAddr`-relative
address (three expressions, two copies), the memory words with their replay,
and, for a call result, the temporary's declaration, read and store. -/
@[simp] theorem sharpSource_global (B n : Nat) :
    sharpSourceWeights.score (WorkEvent.globalAccess n).units + (B + 5) * replayUnits [.globalAccess n] =
      40 + 17 * n + (B + 5) * (n - 1) := by
  simp [sharpSourceWeights, Work.score, WorkEvent.units, replayUnits]

theorem sharpExprScore_le_source (B : Nat) (ev : List WorkEvent) :
    sharpExprScore B ev ≤ sharpSourceScore B ev := by
  simp only [sharpExprScore, sharpSourceScore, Work.score, sharpExprWeights, sharpSourceWeights]
  omega

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

/-- Compiled expression work at exact Loop prices is paid by the source
expression's own events, for every successful expression at certified sites. -/
theorem compiled_expression_sharp_work {F : Type} (B : Nat) (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (structs : s.structs = [])
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (sites : sharpSites B expression = true) :
    sharpCrepList (compileExpExactHOLW context expression).1 ≤
      sharpSourceScore B (expressionEvents s expression) := by
  have present := expression_success_locals_present s expression value evaluated
  have layout := scopedWidthsFit_of_related_present s context targetLocals related expression present
  have lowering := sharp_lowering_bound context expression
  have source := sharp_expression_bound s context B structs expression layout sites
    (by rw [evaluated]; simp)
  have weights := sharpExprScore_le_source B (expressionEvents s expression)
  unfold flattenedSharpWork at lowering
  omega

/-- The replay certificate used by the sharp statement transfer: every
multiword-load address at an executed site has context-free price at most 40. -/
def sharpReplayBound : Nat := 40

/-- Sharp source score at the fixed replay certificate. -/
abbrev sharpScore (ev : List WorkEvent) : Nat := sharpSourceScore sharpReplayBound ev

theorem sharpScore_nil : sharpScore [] = 0 := sharpSourceScore_nil _

theorem sharpScore_append (a b : List WorkEvent) :
    sharpScore (a ++ b) = sharpScore a + sharpScore b := sharpSourceScore_append _ a b

theorem sharpScore_statement (rest : List WorkEvent) :
    sharpScore (.statement :: rest) = 10 + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_statement]

theorem sharpScore_expression (rest : List WorkEvent) :
    sharpScore (.expression :: rest) = 5 + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_expression]

theorem sharpScore_copy (n : Nat) (rest : List WorkEvent) :
    sharpScore (.copy n :: rest) = 5 * n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_copy]

theorem sharpScore_frame (n : Nat) (rest : List WorkEvent) :
    sharpScore (.frame n :: rest) = 4 * n + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_frame]

theorem sharpScore_scalar (n : Nat) (rest : List WorkEvent) :
    sharpScore (.scalar n :: rest) = sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_scalar, Nat.zero_add]

theorem sharpScore_memory (n : Nat) (rest : List WorkEvent) :
    sharpScore (.memory n :: rest) = 12 * n + 45 * (n - 1) + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_memory, sharpReplayBound]

theorem sharpScore_global (n : Nat) (rest : List WorkEvent) :
    sharpScore (.globalAccess n :: rest) = 40 + 17 * n + 45 * (n - 1) + sharpScore rest := by
  simp only [sharpScore, sharpSourceScore_cons, sharpSource_global, sharpReplayBound]

/-- Expression form at the fixed certificate. -/
theorem compiled_expression_sharp_score {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (structs : s.structs = [])
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : expressionValue s expression = some value)
    (sites : sharpSites sharpReplayBound expression = true) :
    sharpCrepList (compileExpExactHOLW context expression).1 ≤ sharpScore (expressionEvents s expression) :=
  compiled_expression_sharp_work sharpReplayBound s context targetLocals related structs expression value
    evaluated sites

#print axioms compiled_expression_sharp_work
end InitECandidate.Runtime.FineCost
