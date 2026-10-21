import InitECandidate.Runtime.SSAReturningContinuationCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- A selected exception handler restores the actual saved cut and binds its
exception value from convention register 2. The emitted refresh/binder work
and handler body use the same source scheduler witness. -/
theorem ssa_returning_exception_continuation {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (names : Spt Unit) (counter name : Nat) (value : WordLocW 64)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : nextVarRename name moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (below : name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → SSAQuantitativeSimulation SP TP body st ct map na lt) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {setVar name value source with permute := permutation}
      let sourceRun := evaluate body sourceState
      let targetRun := evaluate (.seq retMove (.seq (.move 1 [(renamed,2)]) compiled)) (setVar 2 value target)
      sourceRun.1 = some .error ∨
        sourceRun.1 = targetRun.1 ∧ Flapjack.WordAlloc.wordStateEqRel sourceRun.2 targetRun.2 ∧
        SSAResultLocals finalNext finalMap tables sourceRun.2.locals targetRun.2.locals sourceRun.1 ∧
        wordExecutionCost (fun p _ => TP p)
          (.seq retMove (.seq (.move 1 [(renamed,2)]) compiled)) (setVar 2 value target) ≤
          24 * (((sptToAList names).map Prod.fst).length + 1) +
            wordExecutionCost (fun p _ => SP p) body sourceState := by
  have listProduced : listNextVarRename [name] moveMap bindNext = ([renamed],retMap,retNext) := by
    simp only [listNextVarRename,renameProduced]
  have continuation := ssa_returning_general_continuation SP TP body source target ssa targetPrices names counter [name] [value]
    tables retMove moveMap moveNext bindNext [renamed] retMap retNext compiled finalMap finalNext
    moveProduced listProduced bodyProduced bindingIncrease bindingClass related valid stackClass
    sourceDomain rfl (by simp) (by simpa using below) bodyBounds frame tableValid bodyIH
  exact continuation

#print axioms ssa_returning_exception_continuation
end InitECandidate.Runtime.FineCost
