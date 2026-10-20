import InitECandidate.Runtime.SourceCostCrepDecCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The only source primitive takes three words and returns a two-word record. -/
theorem primop_shape {operator : PrimOp} {values : List (ValueHOL 64)} {value : ValueHOL 64}
    (operation : panPrimopHOLExact operator values = some value) :
    (values.flatMap flattenHOL).length = 3 ∧ shapeOfHOLExact value = .comb [.one, .one] ∧
      (flattenHOL value).length = 2 := by
  unfold panPrimopHOLExact at operation
  split at operation
  · simp only [Option.some.injEq] at operation
    subst operation
    simp [flattenHOL, shapeOfHOLExact]
  · simp at operation

theorem bounded_primitive (names : List Nat) (operator : PrimOp) (args : List Nat) :
    CrepBounded (.primitive names operator args) (1 + names.length + args.length) :=
  fun _ t => ⟨_, CrepWork.primitive t names operator args, Nat.le_refl _⟩

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
    (checkedArgs : bulkLoadSitesExps arguments = true) :
    CrepWorkPaid t (compileProgExactHOLW context (.primitive name operator arguments))
      (.statement :: (expressionListEvents s arguments ++ [.scalar 1] ++
        [.copy (flattenHOL value).length])) := by
  classical
  obtain ⟨argWords, valueShape, valueWords⟩ := primop_shape operation
  have localisedArgs : everyExpListHOL localisedExpHOL arguments = true := by
    simpa [localisedProgHOL] using localised
  have targetArgs := pcCompileCorrectCallTargetArgs s t context arguments values args rel.state
    rel.code rel.locals localisedArgs
  have flatLength := opt_mmap_length_eq _ _ _ targetArgs
  rw [argWords] at flatLength
  have argsPaid := arguments_paid rel arguments values args checkedArgs
  unfold CrepWorkPaid
  simp only [compileProgExactHOLW, compilePrimitiveExactHOLW]
  rw [score_statement_cons, score_append, score_append, executionWork_score_cons,
    executionWork_score_cons, valueWords]
  generalize sourceCrepWeights.score (executionWork (expressionListEvents s arguments)) = A
    at argsPaid ⊢
  simp only [executionWork, WorkEvent.units, Work.score, sourceCrepWeights]
  split
  · obtain ⟨w, work, bound⟩ := bounded_skip F t
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
    have decs := bounded_nestedDecs
      ((List.range ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length).map
        (fun index => context.vmax + index + 1))
      ((compileExpExactHOLWList context arguments).flatMap Prod.fst)
      (bounded_primitive names operator
        ((List.range ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length).map
          (fun index => context.vmax + index + 1)))
    obtain ⟨w, work, bound⟩ := decs F t
    refine ⟨w, work, ?_⟩
    simp only [List.length_map, List.length_range, namesLength, flatLength] at bound
    omega

#print axioms primitive_transfer
end InitECandidate.Runtime.FineCost
