import InitECandidate.Runtime.CrepSharpDecCall
import InitECandidate.Runtime.SourceCostSharpCrepPrimitive
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace SharpModel
variable (M : SharpModel) {fn : Flapjack.Pancake.PanLang.MlS}

theorem bounded_primitive (names : List Nat) (operator : PrimOp) (args : List Nat) :
    CrepBoundedM M (.primitive names operator args) (M.S.prim names.length args.length) :=
  fun _ fn t => ⟨_, CrepWorkF.primitive fn t names operator args, Nat.le_refl _⟩

/-- Successful primitives: argument expressions are charged by their events;
fixed-size temporaries and destination slots by the statement and copy events. -/
theorem primitive_transfer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {name : MlStringHOL}
    {operator : PrimOp} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {value : ValueHOL 64}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (operation : panPrimopHOLExact operator values = some value)
    (valid : isValidValueHOLFinite s .local name value = true)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.primitive name operator arguments) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context (.primitive name operator arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (primitiveOverhead (values.flatMap flattenHOL).length)] ++
        [.copy (flattenHOL value).length])) 0 := by
  classical
  obtain ⟨argWords, valueShape, valueWords⟩ := primop_shape_sharp operation
  have localisedArgs : everyExpListHOL localisedExpHOL arguments = true := by
    simpa [localisedProgHOL] using localised
  have targetArgs := pcCompileCorrectCallTargetArgs s t context arguments values args rel.state
    rel.code rel.locals localisedArgs
  have flatLength := opt_mmap_length_eq _ _ _ targetArgs
  rw [argWords] at flatLength
  have argsPaid := M.arguments_paid rel arguments values args localisedArgs
  have prim := M.primOk
  unfold CrepWorkPaidM
  simp only [compileProgExactHOLW, compilePrimitiveExactHOLW]
  rw [sharpScore_statement, sharpScore_append, sharpScore_append, valueWords, argWords]
  generalize sharpScore ((expressionListEvents s arguments)) = A
    at argsPaid ⊢
  simp only [sharpScore_statement, sharpScore_cost, sharpScore_copy, sharpScore_nil]
  split
  · obtain ⟨w, work, bound⟩ := M.bounded_skip F fn t
    exact ⟨w, work, by omega⟩
  · rename_i shape names hlookup
    cases hold : s.locals.lookup name with
    | none =>
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hold] at valid
    | some old =>
    have hse : shapeOfHOLExact value = shapeOfHOLExact old := by
      have : shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact old) = true := by
        simpa [isValidValueHOLFinite, lookupKvarHOLFinite, hold] using valid
      exact (shapeEqHOL_eq_true _ _).mp this
    obtain ⟨ns, words, hvar, hmm, hfl, hwfo⟩ := rel.locals.2.2 name old hold
    rw [hlookup] at hvar
    simp only [Option.some.injEq, Prod.mk.injEq] at hvar
    obtain ⟨_, rfl⟩ := hvar
    have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
    have namesLength : names.length = 2 := by
      rw [opt_mmap_length_eq _ _ _ hmm, ← hfl, hflo, ← hse, valueShape]
      simp [sizeOfShapeHOL, sizeOfShapesHOL]
    have decs := M.bounded_nestedDecs
      ((List.range ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length).map
        (fun index => context.vmax + index + 1))
      ((compileExpExactHOLWList context arguments).flatMap Prod.fst)
      (M.bounded_primitive names operator
        ((List.range ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length).map
          (fun index => context.vmax + index + 1)))
    obtain ⟨w, work, bound⟩ := decs F fn t
    refine ⟨w, work, ?_⟩
    simp only [List.length_map, List.length_range, namesLength, flatLength] at bound
    generalize primitiveOverhead 3 = P at prim ⊢
    omega

end SharpModel

#print axioms SharpModel.primitive_transfer
end InitECandidate.Runtime.FineCost
