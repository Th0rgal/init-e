import InitECandidate.Runtime.SourceCostGlobalsRunDecCall
import Flapjack.Pancake.Proofs.PanGlobals.ReadBytearray
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem globals_external_words {F : Type} {s post : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {configuration configurationLength array arrayLength : ExpHOL 64} {result}
    (run : evaluateHOLFiniteState s
      (.extCall function configuration configurationLength array arrayLength) = (result, post))
    (ok : result ≠ some .error) :
    ∃ a n b m first second,
      expressionValue s configuration = some (.val (.word a)) ∧
      expressionValue s configurationLength = some (.val (.word n)) ∧
      expressionValue s array = some (.val (.word b)) ∧
      expressionValue s arrayLength = some (.val (.word m)) ∧
      sourceReadBytes s a n = some first ∧ sourceReadBytes s b m = some second := by
  rw [evaluateHOLFiniteState_extCall_source] at run
  split at run
  · split at run
    · rename_i _ _ _ _ a n b m h1 h2 h3 h4 _ _ first second r1 r2
      exact ⟨a, n, b, m, first, second, h1, h2, h3, h4, r1, r2⟩
    · exact absurd (Prod.mk.inj run).1.symm ok
  · exact absurd (Prod.mk.inj run).1.symm ok

theorem globalsRel_ffi {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t) :
    s.ffi = t.ffi := by
  unfold panGlobalsStateRelHOLExact at rel
  exact rel.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem globals_readBytes {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    {address length : BitVec 64} {bytes : List (BitVec 8)}
    (h : sourceReadBytes s address length = some bytes) : sourceReadBytes t address length = some bytes :=
  PanGlobalsReadBytearray.stateRelReadBytearray b context s t bytes address length.toNat ⟨rel, h⟩

theorem globals_external (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {configuration configurationLength array arrayLength : ExpHOL 64} {result}
    (run : evaluateHOLFiniteState s
      (.extCall function configuration configurationLength array arrayLength) = (result, post)) :
    GlobalsLe B s (.extCall function configuration configurationLength array arrayLength) result post
      (externalEvents s function configuration configurationLength array arrayLength) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  obtain ⟨a, n, b, m, first, second, h1, h2, h3, h4, r1, r2⟩ := globals_external_words run ok
  have e1 := globals_expression_le B rel configuration ready.1.1.1 (by rw [h1]; simp)
  have e2 := globals_expression_le B rel configurationLength ready.1.1.2 (by rw [h2]; simp)
  have e3 := globals_expression_le B rel array ready.1.2 (by rw [h3]; simp)
  have e4 := globals_expression_le B rel arrayLength ready.2 (by rw [h4]; simp)
  have transfer : externalTransferEvents t function (compileExpExactHOL context configuration)
      (compileExpExactHOL context configurationLength) (compileExpExactHOL context array)
      (compileExpExactHOL context arrayLength) =
      externalTransferEvents s function configuration configurationLength array arrayLength := by
    simp only [externalTransferEvents, globals_value rel h1, globals_value rel h2, globals_value rel h3,
      globals_value rel h4, h1, h2, h3, h4, globals_readBytes rel r1, globals_readBytes rel r2, r1, r2,
      globalsRel_ffi rel]
  simp only [compileProgExactHOL] at target
  cases target
  rw [externalEvents, externalEvents, transfer]
  gsimp
  omega

#print axioms globals_external

theorem globals_sharedLoad (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {operator}
    {kind : VarKind} {name : MlStringHOL} {address : ExpHOL 64} {result}
    (run : evaluateHOLFiniteState s (.shMemLoad operator kind name address) = (result, post)) :
    GlobalsLe B s (.shMemLoad operator kind name address) result post
      (sharedLoadEvents s kind name address) := by
  intro context t rel ok ready code h cov r' t' ev' target
  cases kind with
  | «global» => simp [globalsReadyProg] at ready
  | «local» =>
  simp only [globalsReadyProg] at ready
  have word : ∃ w, expressionValue s address = some (.val (.word w)) := by
    rw [evaluateHOLFiniteState_shMemLoad_source] at run
    split at run
    · rename_i a1 h1; exact ⟨a1, h1⟩
    · exact absurd (Prod.mk.inj run).1.symm ok
  obtain ⟨w, hw⟩ := word
  have e := globals_expression_le B rel address ready (by rw [hw]; simp)
  have locals := globalsRel_locals rel
  simp only [compileProgExactHOL] at target
  cases target
  rw [sharedLoadEvents, sharedLoadEvents, globals_value rel hw, hw]
  simp only [lookupKvarHOLFinite, ← locals, srcScore_statement, sharpSourceScore_append]
  omega

theorem globals_sharedStore (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {operator}
    {address value : ExpHOL 64} {result}
    (run : evaluateHOLFiniteState s (.shMemStore operator address value) = (result, post)) :
    GlobalsLe B s (.shMemStore operator address value) result post (sharedStoreEvents s address value) := by
  intro context t rel ok ready code h cov r' t' ev' target
  simp only [globalsReadyProg, Bool.and_eq_true] at ready
  have words : ∃ a v, expressionValue s address = some (.val (.word a)) ∧
      expressionValue s value = some (.val (.word v)) := by
    rw [evaluateHOLFiniteState_shMemStore_total] at run
    simp only [] at run
    split at run
    · rename_i a1 w1 h1 h2; exact ⟨a1, w1, h1, h2⟩
    · exact absurd (Prod.mk.inj run).1.symm ok
  obtain ⟨a, v, ha, hv⟩ := words
  have e1 := globals_expression_le B rel address ready.1 (by rw [ha]; simp)
  have e2 := globals_expression_le B rel value ready.2 (by rw [hv]; simp)
  simp only [compileProgExactHOL] at target
  cases target
  rw [sharedStoreEvents, sharedStoreEvents, globals_isWord rel (by rw [ha]; simp),
    globals_isWord rel (by rw [hv]; simp)]
  gsimp
  omega

#print axioms globals_sharedLoad
#print axioms globals_sharedStore
end InitECandidate.Runtime.FineCost
