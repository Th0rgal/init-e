import InitECandidate.Runtime.CrepSharpPrimitive
import InitECandidate.Runtime.SourceCostSharpCrepAtomic
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace SharpModel
variable (M : SharpModel) {fn : Flapjack.Pancake.PanLang.MlS}

theorem bounded_dec (name : Nat) (value : CrepExpHOL 64) {body : CrepProgHOL 64} {b : Nat}
    (bodyBounded : CrepBoundedM M body b) :
    CrepBoundedM M (.dec name value body) (M.pr value + b) := by
  intro σ fn t
  rcases evaluated : evalCrepSemHOLExp t value with _ | word
  · exact ⟨_, CrepWorkF.decFailure (fn := fn) evaluated, by omega⟩
  · obtain ⟨w, work, bound⟩ := bodyBounded σ fn { t with locals := t.locals.updateEq (name, word) }
    exact ⟨_, CrepWorkF.dec evaluated work, by omega⟩

theorem word_paid {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {word : BitVec 64}
    {ce : CrepExpHOL 64}
    (evaluated : expressionValue s expression = some (.val (.word word)))
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL expression = true)
    (compiled : compileExpExactHOLW context expression = ([ce], .one)) :
    M.pr ce ≤ sharpScore ((expressionEvents s expression)) := by
  have bound := M.expression_paid s context t.locals rel.locals expression _
    evaluated localised
  rw [compiled] at bound
  simp only [prs_cons, prs_nil] at bound
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
    (checked : sharpSitesProg sharpReplayBound
      (.extCall function configuration configurationLength array arrayLength) = true) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context
        (.extCall function configuration configurationLength array arrayLength))
      (externalEvents s function configuration configurationLength array arrayLength) 0 := by
  classical
  simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_extCall_source] at run
  split at run
  · rename_i a1 l1 a2 l2 h1 h2 h3 h4
    obtain ⟨c1, e1⟩ := compiled_word_sharp h1 rel localised.1.1.1
    obtain ⟨c2, e2⟩ := compiled_word_sharp h2 rel localised.1.1.2
    obtain ⟨c3, e3⟩ := compiled_word_sharp h3 rel localised.1.2
    obtain ⟨c4, e4⟩ := compiled_word_sharp h4 rel localised.2
    have p1 := M.word_paid h1 rel localised.1.1.1 e1
    have p2 := M.word_paid h2 rel localised.1.1.2 e2
    have p3 := M.word_paid h3 rel localised.1.2 e3
    have p4 := M.word_paid h4 rel localised.2 e4
    unfold CrepWorkPaidM externalEvents
    rw [sharpScore_statement, sharpScore_cost, sharpScore_append, sharpScore_append, sharpScore_append,
      sharpScore_append]
    simp only [compileProgExactHOLW, compileExtCallExactHOLW, e1, e2, e3, e4]
    have ffi := M.ffiOk
    obtain ⟨w, work, bound⟩ := (M.bounded_dec _ c1 (M.bounded_dec _ c2 (M.bounded_dec _ c3
      (M.bounded_dec _ c4 (fun _ fn t => ⟨_, CrepWorkF.extCall fn t function _ _ _ _, Nat.le_refl _⟩)))))
      F fn t
    refine ⟨w, work, ?_⟩
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 p2 p3 p4 ⊢
    omega
  · exact absurd (Prod.mk.inj run).1.symm resultOk

theorem shared_store_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {operator : OpSize}
    {address value : ExpHOL 64} {result : Option (PanSemResultExact 64)}
    (run : evaluateHOLFiniteState s (.shMemStore operator address value) = (result, post))
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.shMemStore operator address value) = true)
    (checked : sharpSitesProg sharpReplayBound (.shMemStore operator address value) = true) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context (.shMemStore operator address value))
      (sharedStoreEvents s address value) 0 := by
  classical
  simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
  rw [evaluateHOLFiniteState_shMemStore_total] at run
  simp only [] at run
  split at run
  · rename_i a1 w1 h1 h2
    obtain ⟨c1, e1⟩ := compiled_word_sharp h1 rel localised.1
    obtain ⟨c2, e2⟩ := compiled_word_sharp h2 rel localised.2
    have p1 := M.word_paid h1 rel localised.1 e1
    have p2 := M.word_paid h2 rel localised.2 e2
    have h1' : expressionValue s address = some (.val (.word a1)) := h1
    have h2' : expressionValue s value = some (.val (.word w1)) := h2
    have w1 : expressionIsWord s address = true := by unfold expressionIsWord; rw [h1']
    have w2 : expressionIsWord s value = true := by unfold expressionIsWord; rw [h2']
    unfold CrepWorkPaidM sharedStoreEvents
    rw [sharpScore_statement, sharpScore_append, sharpScore_append]
    simp only [w1, w2, Bool.and_self, if_true, sharpScore_native, sharpScore_nil]
    simp only [compileProgExactHOLW, compileShMemStoreExactHOLW, e1, e2]
    have sh := M.shMemOk
    obtain ⟨w, work, bound⟩ := (M.bounded_dec _ c2
      (fun _ fn t => ⟨_, CrepWorkF.shMem fn t (storeMemOpHOL operator) _ c1, Nat.le_refl _⟩)) F fn t
    refine ⟨w, work, ?_⟩
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 p2 ⊢
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
    (checked : sharpSitesProg sharpReplayBound (.shMemLoad operator kind name address) = true) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context (.shMemLoad operator kind name address))
      (sharedLoadEvents s kind name address) 0 := by
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
    have p1 := M.word_paid h1 rel localised e1
    have h1' : expressionValue s address = some (.val (.word a1)) := h1
    unfold CrepWorkPaidM sharedLoadEvents
    rw [sharpScore_statement, sharpScore_append]
    simp only [h1', h2, sharpScore_native, sharpScore_copy, sharpScore_nil]
    simp only [compileProgExactHOLW, compileShMemLoadExactHOLW, e1]
    split
    · have sh := M.shMemOk
      refine ⟨_, CrepWorkF.shMem fn t _ _ c1, ?_⟩
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at p1 ⊢
      omega
    · exact ⟨0, CrepWorkF.skip fn t, by omega⟩
  · exact absurd (Prod.mk.inj run).1.symm resultOk

end SharpModel

#print axioms SharpModel.external_transfer
#print axioms SharpModel.shared_store_transfer
#print axioms SharpModel.shared_load_transfer
end InitECandidate.Runtime.FineCost
