import InitECandidate.Runtime.SourceCostSharpCrepPrimitive
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem sharp_bounded_dec_sharp (name : Nat) (value : CrepExpHOL 64) {body : CrepProgHOL 64} {b : Nat}
    (bodyBounded : CrepBoundedS body b) :
    CrepBoundedS (.dec name value body) (loopNodePrice value + b) := by
  intro σ t
  rcases evaluated : evalCrepSemHOLExp t value with _ | word
  · exact ⟨_, CrepWorkS.decFailure evaluated, by omega⟩
  · obtain ⟨w, work, bound⟩ := bodyBounded σ { t with locals := t.locals.updateEq (name, word) }
    exact ⟨_, CrepWorkS.dec evaluated work, by omega⟩

/-- A successful word expression compiles to one scalar Crep expression. -/
theorem compiled_word_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
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

theorem word_paid_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {word : BitVec 64}
    {ce : CrepExpHOL 64}
    (evaluated : expressionValue s expression = some (.val (.word word)))
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL expression = true)
    (compiled : compileExpExactHOLW context expression = ([ce], .one)) :
    loopNodePrice ce ≤ sharpScore ((expressionEvents s expression)) := by
  have bound := compiled_expression_sharp_score s context t.locals rel.locals expression _
    evaluated localised
  rw [compiled] at bound
  simp only [loopPriceList_cons', loopPriceList_nil'] at bound
  omega

theorem external_transfer_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {function : MlStringHOL}
    {configuration configurationLength array arrayLength : ExpHOL 64}
    {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s
      (.extCall function configuration configurationLength array arrayLength) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL
      (.extCall function configuration configurationLength array arrayLength) = true)
    (checked : sharpSitesProg sharpReplayBound
      (.extCall function configuration configurationLength array arrayLength) = true) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context
        (.extCall function configuration configurationLength array arrayLength))
      (externalEvents s function configuration configurationLength array arrayLength) := by
  classical
  simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_extCall_source] at run
  split at run
  · rename_i a1 l1 a2 l2 h1 h2 h3 h4
    obtain ⟨c1, e1⟩ := compiled_word_sharp h1 rel localised.1.1.1
    obtain ⟨c2, e2⟩ := compiled_word_sharp h2 rel localised.1.1.2
    obtain ⟨c3, e3⟩ := compiled_word_sharp h3 rel localised.1.2
    obtain ⟨c4, e4⟩ := compiled_word_sharp h4 rel localised.2
    have p1 := word_paid_sharp h1 rel localised.1.1.1 e1
    have p2 := word_paid_sharp h2 rel localised.1.1.2 e2
    have p3 := word_paid_sharp h3 rel localised.1.2 e3
    have p4 := word_paid_sharp h4 rel localised.2 e4
    unfold CrepWorkPaid_sharp externalEvents
    rw [sharpScore_statement, sharpScore_cost, sharpScore_append, sharpScore_append, sharpScore_append,
      sharpScore_append]
    simp only [compileProgExactHOLW, compileExtCallExactHOLW, e1, e2, e3, e4]
    obtain ⟨w, work, bound⟩ := (sharp_bounded_dec_sharp _ c1 (sharp_bounded_dec_sharp _ c2 (sharp_bounded_dec_sharp _ c3
      (sharp_bounded_dec_sharp _ c4 (fun _ t => ⟨_, CrepWorkS.extCall t function _ _ _ _, Nat.le_refl 37⟩)))))
      F t
    refine ⟨w, work, ?_⟩
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 p2 p3 p4 ⊢
    omega
  · exact absurd (Prod.mk.inj run).1.symm resultOk

theorem shared_store_transfer_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {operator : OpSize}
    {address value : ExpHOL 64} {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s (.shMemStore operator address value) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.shMemStore operator address value) = true)
    (checked : sharpSitesProg sharpReplayBound (.shMemStore operator address value) = true) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.shMemStore operator address value))
      (sharedStoreEvents s address value) := by
  classical
  simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_shMemStore_total] at run
  simp only [] at run
  split at run
  · rename_i a1 w1 h1 h2
    obtain ⟨c1, e1⟩ := compiled_word_sharp h1 rel localised.1
    obtain ⟨c2, e2⟩ := compiled_word_sharp h2 rel localised.2
    have p1 := word_paid_sharp h1 rel localised.1 e1
    have p2 := word_paid_sharp h2 rel localised.2 e2
    have h1' : expressionValue s address = some (.val (.word a1)) := h1
    have h2' : expressionValue s value = some (.val (.word w1)) := h2
    have w1 : expressionIsWord s address = true := by unfold expressionIsWord; rw [h1']
    have w2 : expressionIsWord s value = true := by unfold expressionIsWord; rw [h2']
    unfold CrepWorkPaid_sharp sharedStoreEvents
    rw [sharpScore_statement, sharpScore_append, sharpScore_append]
    simp only [w1, w2, Bool.and_self, if_true, sharpScore_native, sharpScore_nil]
    simp only [compileProgExactHOLW, compileShMemStoreExactHOLW, e1, e2]
    obtain ⟨w, work, bound⟩ := (sharp_bounded_dec_sharp _ c2
      (fun _ t => ⟨_, CrepWorkS.shMem t (storeMemOpHOL operator) _ c1, Nat.le_refl _⟩)) F t
    refine ⟨w, work, ?_⟩
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 p2 ⊢
    omega
  · exact absurd (Prod.mk.inj run).1.symm resultOk

theorem shared_load_transfer_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {operator : OpSize}
    {kind : VarKind} {name : MlStringHOL} {address : ExpHOL 64}
    {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s (.shMemLoad operator kind name address) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.shMemLoad operator kind name address) = true)
    (checked : sharpSitesProg sharpReplayBound (.shMemLoad operator kind name address) = true) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.shMemLoad operator kind name address))
      (sharedLoadEvents s kind name address) := by
  classical
  cases kind with
  | «global» => simp [localisedProgHOL] at localised
  | «local» =>
  simp only [localisedProgHOL, sharpSitesProg] at localised checked
  rw [evaluateHOLFiniteState_shMemLoad_source] at run
  split at run
  · rename_i a1 h1
    split at run
    rotate_left
    · exact absurd (Prod.mk.inj run).1.symm resultOk
    rename_i v1 h2
    obtain ⟨c1, e1⟩ := compiled_word_sharp h1 rel localised
    have p1 := word_paid_sharp h1 rel localised e1
    have h1' : expressionValue s address = some (.val (.word a1)) := h1
    unfold CrepWorkPaid_sharp sharedLoadEvents
    rw [sharpScore_statement, sharpScore_append]
    simp only [h1', h2, sharpScore_native, sharpScore_copy, sharpScore_nil]
    simp only [compileProgExactHOLW, compileShMemLoadExactHOLW, e1]
    split
    · refine ⟨_, CrepWorkS.shMem t _ _ c1, ?_⟩
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 ⊢
      omega
    · exact ⟨0, CrepWorkS.skip t, by omega⟩
  · exact absurd (Prod.mk.inj run).1.symm resultOk

#print axioms external_transfer_sharp
#print axioms shared_store_transfer_sharp
#print axioms shared_load_transfer_sharp
end InitECandidate.Runtime.FineCost
