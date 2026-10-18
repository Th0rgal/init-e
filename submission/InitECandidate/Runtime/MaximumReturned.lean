import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact original maximum helper execution, including return scope clearing. -/
theorem evaluate_max_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64)
    (left : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (right : state.locals.lookup (ofString "b") = some (.val (.word b))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_max) =
      (some (.returned (.val (.word (if b < a then a else b)))),emptyLocalsHOLFinite state) := by
  rw [sourceFunctionBody_eq_structural]
  change evaluateHOLFiniteState state
    (.seq (.ite (.cmp .lower (.var .local (ofString "b")) (.var .local (ofString "a")))
      (.return (.var .local (ofString "a"))) .skip) (.return (.var .local (ofString "b")))) = _
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  by_cases less : b < a
  all_goals simp [evalHOLFinite_eq_toExact,evalHOLExact,left,right,
    Compiler.Encoders.Asm.wordCmpHOL,less,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
    shapeOfHOLExact,sizeOfShapeWithContextHOL]

theorem max_body_returned_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (value : ValueHOL 64) (bound : Nat)
    (left : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (right : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (leftBound : a.toNat ≤ bound) (rightBound : b.toNat ≤ bound)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_max) =
      (some (.returned value),post)) :
    ∃ result : BitVec 64, value = .val (.word result) ∧ result.toNat ≤ bound ∧
      post = emptyLocalsHOLFinite state := by
  rw [evaluate_max_body state a b left right] at run
  have resultEq := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
  refine ⟨if b < a then a else b,resultEq.symm,?_,(Prod.mk.inj run).2.symm⟩
  split <;> assumption

#print axioms evaluate_max_body
#print axioms max_body_returned_bound
end InitECandidate.Runtime
