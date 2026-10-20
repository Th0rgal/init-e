import InitECandidate.Runtime.SourceCostCrepPrimitive
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem bounded_dec (name : Nat) (value : CrepExpHOL 64) {body : CrepProgHOL 64} {b : Nat}
    (bodyBounded : CrepBounded body b) :
    CrepBounded (.dec name value body) (1 + crepNodeWork value + b) := by
  intro σ t
  rcases evaluated : evalCrepSemHOLExp t value with _ | word
  · exact ⟨_, CrepWork.decFailure evaluated, by omega⟩
  · obtain ⟨w, work, bound⟩ := bodyBounded σ { t with locals := t.locals.updateEq (name, word) }
    exact ⟨_, CrepWork.dec evaluated work, by omega⟩

/-- A successful word expression compiles to one scalar Crep expression. -/
theorem compiled_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    {expression : ExpHOL 64} {word : BitVec 64}
    (evaluated : expressionValue s expression = some (.val (.word word)))
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL expression = true) :
    ∃ ce, compileExpExactHOLW context expression = ([ce], .one) := by
  classical
  rcases hc : compileExpExactHOLW context expression with ⟨es, sh⟩
  obtain ⟨hes, _, hcs, _⟩ :=
    @compileExpValRelHOL 64 F _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) context t
      (fun address => Classical.propDecidable (t.memaddrs address))
      expression (.val (.word word)) es sh evaluated rel.state rel.code rel.locals localised hc
  simp only [shapeOfHOLExact] at hcs
  subst hcs
  rcases es with _ | ⟨ce, _ | ⟨_, _⟩⟩
  · simp [flattenHOL] at hes
  · exact ⟨ce, rfl⟩
  · simp [flattenHOL] at hes

theorem word_paid {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {word : BitVec 64}
    {ce : CrepExpHOL 64}
    (evaluated : expressionValue s expression = some (.val (.word word)))
    (rel : SourceCrepRel context s t) (checked : bulkLoadSitesExp expression = true)
    (compiled : compileExpExactHOLW context expression = ([ce], .one)) :
    crepNodeWork ce ≤ sourceCrepWeights.score (executionWork (expressionEvents s expression)) := by
  have bound := compiled_expression_crep_work s context t.locals rel.locals expression _
    evaluated checked
  rw [compiled] at bound
  simp only [crepListWork] at bound
  unfold expressionCost at bound
  omega

theorem external_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {function : MlStringHOL}
    {configuration configurationLength array arrayLength : ExpHOL 64}
    {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s
      (.extCall function configuration configurationLength array arrayLength) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL
      (.extCall function configuration configurationLength array arrayLength) = true)
    (checked : bulkLoadSitesProg
      (.extCall function configuration configurationLength array arrayLength) = true) :
    CrepWorkPaid t (compileProgExactHOLW context
        (.extCall function configuration configurationLength array arrayLength))
      (externalEvents s function configuration configurationLength array arrayLength) := by
  classical
  simp only [localisedProgHOL, bulkLoadSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_extCall_source] at run
  split at run
  · rename_i a1 l1 a2 l2 h1 h2 h3 h4
    obtain ⟨c1, e1⟩ := compiled_word h1 rel localised.1.1.1
    obtain ⟨c2, e2⟩ := compiled_word h2 rel localised.1.1.2
    obtain ⟨c3, e3⟩ := compiled_word h3 rel localised.1.2
    obtain ⟨c4, e4⟩ := compiled_word h4 rel localised.2
    have p1 := word_paid h1 rel checked.1.1.1 e1
    have p2 := word_paid h2 rel checked.1.1.2 e2
    have p3 := word_paid h3 rel checked.1.2 e3
    have p4 := word_paid h4 rel checked.2 e4
    unfold CrepWorkPaid externalEvents
    rw [score_statement_cons, score_append, score_append, score_append, score_append]
    simp only [compileProgExactHOLW, compileExtCallExactHOLW, e1, e2, e3, e4]
    obtain ⟨w, work, bound⟩ := (bounded_dec _ c1 (bounded_dec _ c2 (bounded_dec _ c3
      (bounded_dec _ c4 (fun _ t => ⟨_, CrepWork.extCall t function _ _ _ _, Nat.le_refl 1⟩)))))
      F t
    refine ⟨w, work, ?_⟩
    simp only [sourceCrepWeights] at p1 p2 p3 p4 ⊢
    omega
  · exact absurd (Prod.mk.inj run).1.symm resultOk

theorem shared_store_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {operator : OpSize}
    {address value : ExpHOL 64} {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s (.shMemStore operator address value) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.shMemStore operator address value) = true)
    (checked : bulkLoadSitesProg (.shMemStore operator address value) = true) :
    CrepWorkPaid t (compileProgExactHOLW context (.shMemStore operator address value))
      (sharedStoreEvents s address value) := by
  classical
  simp only [localisedProgHOL, bulkLoadSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_shMemStore_total] at run
  simp only [] at run
  split at run
  · rename_i a1 w1 h1 h2
    obtain ⟨c1, e1⟩ := compiled_word h1 rel localised.1
    obtain ⟨c2, e2⟩ := compiled_word h2 rel localised.2
    have p1 := word_paid h1 rel checked.1 e1
    have p2 := word_paid h2 rel checked.2 e2
    unfold CrepWorkPaid sharedStoreEvents
    rw [score_statement_cons, score_append, score_append]
    simp only [compileProgExactHOLW, compileShMemStoreExactHOLW, e1, e2]
    obtain ⟨w, work, bound⟩ := (bounded_dec _ c2
      (fun _ t => ⟨_, CrepWork.shMem t (storeMemOpHOL operator) _ c1, Nat.le_refl _⟩)) F t
    refine ⟨w, work, ?_⟩
    simp only [sourceCrepWeights] at p1 p2 ⊢
    omega
  · exact absurd (Prod.mk.inj run).1.symm resultOk

theorem shared_load_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {operator : OpSize}
    {kind : VarKind} {name : MlStringHOL} {address : ExpHOL 64}
    {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s (.shMemLoad operator kind name address) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.shMemLoad operator kind name address) = true)
    (checked : bulkLoadSitesProg (.shMemLoad operator kind name address) = true) :
    CrepWorkPaid t (compileProgExactHOLW context (.shMemLoad operator kind name address))
      (sharedLoadEvents s kind name address) := by
  classical
  cases kind with
  | «global» => simp [localisedProgHOL] at localised
  | «local» =>
  simp only [localisedProgHOL, bulkLoadSitesProg] at localised checked
  rw [evaluateHOLFiniteState_shMemLoad_source] at run
  split at run
  · rename_i a1 h1
    obtain ⟨c1, e1⟩ := compiled_word h1 rel localised
    have p1 := word_paid h1 rel checked e1
    unfold CrepWorkPaid sharedLoadEvents
    rw [score_statement_cons, score_append]
    simp only [compileProgExactHOLW, compileShMemLoadExactHOLW, e1]
    split
    · refine ⟨_, CrepWork.shMem t _ _ c1, ?_⟩
      simp only [sourceCrepWeights] at p1 ⊢
      omega
    · exact ⟨1, CrepWork.skip t, by simp only [sourceCrepWeights]; omega⟩
  · exact absurd (Prod.mk.inj run).1.symm resultOk

#print axioms external_transfer
#print axioms shared_store_transfer
#print axioms shared_load_transfer
end InitECandidate.Runtime.FineCost
