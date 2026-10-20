import InitECandidate.Runtime.PanScalarCostTransfer
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The authoritative compiler locals relation determines exact runtime widths
for variables actually present in source locals. It does not imply that every
compiler-context variable is initialized in the source state. -/
theorem related_local_width {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (name : MlStringHOL) (value : ValueHOL 64) (shape : ShapeHOL) (names : List Nat)
    (present : s.locals.lookup name = some value)
    (mapped : context.vars.lookup name = some (shape, names)) :
    names.length = resultWords s (.var .local name) := by
  obtain ⟨slots, found, width, rest⟩ :=
    panToCrepLocalsRelLookupCtxtFiniteExact context s.locals targetLocals name value related present
  rw [mapped] at found
  have equal := Option.some.inj found
  have namesEqual : names = slots := congrArg Prod.snd equal
  subst slots
  simp only [resultWords, expressionValue, evalHOLExact, toExact, present, Option.map_some, Option.getD_some]
  exact width

/-- Domain coverage is an explicit additional condition. The existing locals
relation is one-way, so dropping this premise would be unsound on absent locals. -/
theorem localWidthsFit_of_related_coverage {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (coverage : ∀ name shape names, context.vars.lookup name = some (shape, names) →
      ∃ value, s.locals.lookup name = some value) :
    LocalWidthsFit s context := by
  intro name shape names mapped
  obtain ⟨value, present⟩ := coverage name shape names mapped
  have width := related_local_width s context targetLocals related name value shape names present mapped
  omega

/-- A successful local-variable read needs no whole-context domain coverage:
its existing compiler locals relation supplies the required width directly. -/
theorem related_local_source_allowance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (context : PanToCrepContextExact 64) (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (name : MlStringHOL) (value : ValueHOL 64) (present : s.locals.lookup name = some value) :
    panLoweringAllowance context (.var .local name) ≤
      expressionCost scalarLoweringWeights s (.var .local name) := by
  obtain ⟨slots, mapped, width, rest⟩ :=
    panToCrepLocalsRelLookupCtxtFiniteExact context s.locals targetLocals name value related present
  have actualWidth := related_local_width s context targetLocals related name value
    (shapeOfHOLExact value) slots present mapped
  simp only [panLoweringAllowance, mapped]
  unfold expressionCost
  rw [expressionEvents]
  simp [executionWork, Work.score, Work.plus, WorkEvent.units, scalarLoweringWeights]
  omega

/-- Direct local-read source cost to executed Loop work, using the actual
compiler locals relation rather than an unexplained whole-context width premise. -/
theorem related_local_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (name : MlStringHOL) (value : ValueHOL 64) (present : s.locals.lookup name = some value)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 G) :
    let expressions := (compileExpExactHOLW context (.var .local name)).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopValuesWork compiled.2.1 + compiled.2.1.length ≤
        6 * expressionCost scalarLoweringWeights s (.var .local name) := by
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace context loopContext tmp live
    (.var .local name) state
  exact ⟨cost, trace, Nat.le_trans bound (Nat.mul_le_mul_left 6
    (related_local_source_allowance s context targetLocals related name value present))⟩

#print axioms related_local_source_to_loop_cost

/-- Context entries unrelated to the expression need no coverage. -/
theorem scopedWidthsFit_of_related_present {F : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64)
    (presentReads : ∀ name, name ∈ varExpHOL expression →
      ∃ value, s.locals.lookup name = some value) :
    LocalWidthsFitOn s context (varExpHOL expression) := by
  intro name member shape names mapped
  obtain ⟨value, present⟩ := presentReads name member
  have width := related_local_width s context targetLocals related name value shape names present mapped
  omega

/-- Compound scalar expressions use only read-local presence and the existing
compiler relation; arbitrary extra context entries are harmless. -/
theorem related_scalar_source_to_loop_cost {F G : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (expression : ExpHOL 64)
    (presentReads : ∀ name, name ∈ varExpHOL expression →
      ∃ value, s.locals.lookup name = some value)
    (supported : scalarLowering expression = true)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 G) :
    let expressions := (compileExpExactHOLW context expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopValuesWork compiled.2.1 + compiled.2.1.length ≤
        6 * expressionCost scalarLoweringWeights s expression := by
  have layout := scopedWidthsFit_of_related_present s context targetLocals related expression presentReads
  obtain ⟨cost, trace, bound⟩ := compiled_pan_expression_trace context loopContext tmp live expression state
  exact ⟨cost, trace, Nat.le_trans bound (Nat.mul_le_mul_left 6
    (scoped_scalar_lowering_cost_bound s context expression layout supported))⟩

#print axioms related_scalar_source_to_loop_cost

#print axioms related_local_width
#print axioms localWidthsFit_of_related_coverage
end InitECandidate.Runtime.FineCost
