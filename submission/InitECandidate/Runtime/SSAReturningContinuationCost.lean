import InitECandidate.Runtime.SSAQuantitativeCost
import InitECandidate.Runtime.SSALoopSetupExecutedCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Actual successful-return binder and continuation, with one scheduler
witness for semantic transport and executed cost. Original compiler equations
and cut/binding invariants derive both emitted move runs. Only the smaller
continuation-body quantitative IH remains; emitted move work is proved here. -/
theorem ssa_returning_general_continuation {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW 64))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → SSAQuantitativeSimulation SP TP body st ct map na lt) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let prepared := setVars registers values target
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {setVars returns values source with permute := permutation}
      let sourceRun := evaluate body sourceState
      let targetRun := evaluate (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        SSAResultLocals finalNext finalMap tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
        wordExecutionCost (fun p _ => TP p)
          (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared ≤
          24 * (((sptToAList names).map Prod.fst).length + returns.length) +
            wordExecutionCost (fun p _ => SP p) body sourceState := by
  classical
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let prepared := WordSemStateFiniteExact.setVars registers values target
  have allocated := isStackVarFlip counter stackClass
  have nonphysical : ¬ isPhyVar (counter+2) := ((conventionPartitions _).2.2.mp allocated).1
  have restoration := returningRestoreRegistersRead source target ssa names counter returns.length
    values related valid sourceDomain lengths.symm nonphysical frame
  rw [moveProduced] at restoration
  dsimp only at restoration
  rcases run : WordSemStateFiniteExact.evaluate retMove prepared with ⟨result,refreshed⟩
  change WordSemStateFiniteExact.evaluate retMove prepared = _ at run
  change (WordSemStateFiniteExact.evaluate retMove prepared).1 = none ∧
    ssaLocalsRel moveNext moveMap source.locals (WordSemStateFiniteExact.evaluate retMove prepared).2.locals ∧
    Flapjack.WordAlloc.wordStateEqRel source (WordSemStateFiniteExact.evaluate retMove prepared).2 ∧
    WordSemStateFiniteExact.getVars registers (WordSemStateFiniteExact.evaluate retMove prepared).2 =
      some values at restoration
  rw [run] at restoration
  dsimp only at restoration
  obtain ⟨normal,refreshedRelated,refreshedFrame,reread⟩ := restoration
  subst result
  have moveProps := listNextVarRenameMoveProps _ (sptInter ssa names) (counter+2)
    retMove moveMap moveNext moveProduced
    ⟨Or.inl allocated,ssaMapOKMore counter _ (counter+2)
      ⟨ssaMapOKInter counter ssa names valid,by omega⟩⟩
  have bindingRelated := ssaLocalsRelMore moveNext moveMap source.locals refreshed.locals bindNext
    ⟨refreshedRelated,bindingIncrease⟩
  have bindingValid := ssaMapOKMore moveNext moveMap bindNext ⟨moveProps.2.2.2,bindingIncrease⟩
  have retProps := listNextVarRenameProps returns moveMap bindNext renamed retMap retNext
    renameProduced ⟨Or.inl bindingClass,bindingValid⟩
  have movedBelow : ∀ name ∈ returns, name < bindNext := by
    intro name member
    have := below name member
    omega
  have binding := returningBindResults source refreshed moveMap bindNext returns values
    bindingRelated bindingValid ((conventionPartitions _).2.2.mp bindingClass).1
    movedBelow distinct lengths reread refreshedFrame
  rw [renameProduced] at binding
  dsimp only at binding
  obtain ⟨copyRun,copyRelated,copyFrame⟩ := binding
  have boundIncrease : counter ≤ retNext := by omega
  have finalBodyBounds : everyVarHOL (fun key => decide (key < retNext)) body = true := Flapjack.everyVarMono _ body _
    ⟨fun key bound => by
      simp only [decide_eq_true_eq] at bound ⊢
      exact Nat.lt_of_lt_of_le bound boundIncrease,bodyBounds⟩
  obtain ⟨permutation,post⟩ := bodyIH
    (WordSemStateFiniteExact.setVars returns values source)
    (WordSemStateFiniteExact.setVars renamed values refreshed) retMap retNext tables
    ⟨copyFrame,copyRelated,retProps.2.1 bindingClass,finalBodyBounds,retProps.2.2.2,tableValid⟩
  refine ⟨permutation, ?_⟩
  dsimp only at post ⊢
  rw [bodyProduced] at post
  have targetRun : evaluate (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared =
      evaluate compiled (setVars renamed values refreshed) := by
    rw [evaluate, fix_clock_evaluate, run]
    change evaluate (.seq (.move 1 (renamed.zip registers)) compiled) refreshed = _
    rw [evaluate, fix_clock_evaluate, copyRun]
  rw [targetRun]
  rcases post with error | ⟨same, postFrame, postLocals, bodyCost⟩
  · exact Or.inl error
  · refine Or.inr ⟨same, postFrame, postLocals, ?_⟩
    have prices : ∀ p (state : WordSemStateFiniteExact 64 C F),
        TP p ≤ wordOptimizerLocalPrice p state := by
      intro p state
      rw [← wordOptimizerLocalPrice_state_independent p target state]
      exact targetPrices p
    have refreshCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p) retMove prepared ≤
        24 * ((sptToAList names).map Prod.fst).length := by
      have comparison := wordExecutionCost_mono (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
        wordOptimizerLocalPrice prices retMove prepared
      have exactCost := optimizer_refresh_move_cost (sptInter ssa names) (counter+2)
        ((sptToAList names).map Prod.fst) prepared
      rw [moveProduced] at exactCost
      exact comparison.trans (Nat.le_of_eq exactCost)
    have bindCost : TP (.move 1 (renamed.zip registers)) ≤ 24 * returns.length := by
      have bound := targetPrices (.move 1 (renamed.zip registers))
      simp only [wordOptimizerLocalPrice, List.length_zip] at bound
      have size : registers.length = returns.length := by simp [registers]
      exact bound.trans (by rw [← size]; exact Nat.mul_le_mul_left 24 (Nat.min_le_right _ _))
    have head1 : TP (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) = 0 := by
      have bound := targetPrices (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled))
      change _ ≤ 0 at bound
      omega
    have head2 : TP (.seq (.move 1 (renamed.zip registers)) compiled) = 0 := by
      have bound := targetPrices (.seq (.move 1 (renamed.zip registers)) compiled)
      change _ ≤ 0 at bound
      omega
    rw [wordExecutionCost_seq, run]
    simp only
    rw [wordExecutionCost_seq, copyRun]
    simp only
    rw [wordExecutionCost_atomic _ (.move 1 (renamed.zip registers)) _ rfl]
    rw [head1, head2]
    dsimp only [prepared, registers] at refreshCost bindCost bodyCost ⊢
    omega

/-- Immediate return-result binding uses the emitted refresh counter itself. -/
theorem ssa_returning_normal_continuation {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW 64))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → SSAQuantitativeSimulation SP TP body st ct map na lt) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let prepared := setVars registers values target
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {setVars returns values source with permute := permutation}
      let sourceRun := evaluate body sourceState
      let targetRun := evaluate (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        SSAResultLocals finalNext finalMap tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
        wordExecutionCost (fun p _ => TP p)
          (.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)) prepared ≤
          24 * (((sptToAList names).map Prod.fst).length + returns.length) +
            wordExecutionCost (fun p _ => SP p) body sourceState := by
  have allocated := isStackVarFlip counter stackClass
  have moveProps := listNextVarRenameMoveProps _ (sptInter ssa names) (counter+2)
    retMove moveMap moveNext moveProduced
    ⟨Or.inl allocated,ssaMapOKMore counter _ (counter+2)
      ⟨ssaMapOKInter counter ssa names valid,by omega⟩⟩
  exact ssa_returning_general_continuation SP TP body source target ssa targetPrices names counter returns values tables
    retMove moveMap moveNext moveNext renamed retMap retNext compiled finalMap finalNext
    moveProduced renameProduced bodyProduced (Nat.le_refl _) (moveProps.2.1 allocated)
    related valid stackClass sourceDomain lengths distinct below bodyBounds frame tableValid bodyIH

#print axioms ssa_returning_normal_continuation
#print axioms ssa_returning_general_continuation
end InitECandidate.Runtime.FineCost
