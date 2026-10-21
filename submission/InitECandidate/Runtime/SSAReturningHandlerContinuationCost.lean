import InitECandidate.Runtime.SSAReturningExceptionCost
import InitECandidate.Runtime.SSAAppendReconciliationCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Execute the selected handler through its real SSA reconciliation. The
compiler's right-branch theorem supplies the move semantics; exact emitted
leaf work is charged only as an upper bound. The source scheduler witness,
body-entry allowance and final locals relation are composed in one result. -/
theorem ssa_returning_handler_continuation_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (bodyEntry : Spt Nat → Nat → Nat)
    (body : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (names : Spt Unit) (counter name : Nat) (value : WordLocW 64)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (bodyMap : Spt Nat) (bodyNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : nextVarRename name moveMap bindNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,bodyMap,bodyNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (below : name < counter)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) (tableValid : ltOK tables)
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (leftMap finalMap : Spt Nat) (finalNext : Nat)
    (prio : Option (Unit ⊕ Unit)) (normalMoves exceptionMoves : WordLangProgHOL (BitVec 64))
    (reconcileProduced : fixInconsistencies prio leftMap bodyMap bodyNext =
      (normalMoves,exceptionMoves,finalNext,finalMap))
    (allocated : isAllocVar bodyNext) (bodyValid : ssaMapOK bodyNext bodyMap)
    (reconciliationWork : Nat)
    (reconciliationLine : lineBound (ssaReconciliationLeaf TP) exceptionMoves = some reconciliationWork)
    (bodyIH : SSABodyAllowance (C := C) (F := F) SP TP body retMap retNext tables (bodyEntry retMap retNext)) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {setVar name value source with permute := permutation}
      let sourceRun := evaluate body sourceState
      let targetProgram := WordLangProgHOL.seq
        (.seq retMove (.seq (.move 1 [(renamed,2)]) compiled)) exceptionMoves
      let targetState := setVar 2 value target
      SSAQuantitativeOutcome finalMap finalNext tables sourceRun (evaluate targetProgram targetState)
        (TP retMove + TP (.move 1 [(renamed,2)]) + bodyEntry retMap retNext +
          wordExecutionCost (fun p _ => SP p) body sourceState + reconciliationWork)
        (wordExecutionCost (fun p _ => TP p) targetProgram targetState) := by
  obtain ⟨permutation,post⟩ := ssa_returning_exception_continuation_entry SP TP bodyEntry
    body source target ssa targetPrices names counter name value tables retMove moveMap moveNext
    bindNext renamed retMap retNext compiled bodyMap bodyNext moveProduced renameProduced
    bodyProduced bindingIncrease bindingClass related valid stackClass sourceDomain below
    bodyBounds frame tableValid bodyIH
  refine ⟨permutation, ?_⟩
  have moveSpec : ∀ (st ct : WordSemStateFiniteExact 64 C F),
      ssaLocalsRel bodyNext bodyMap st.locals ct.locals →
      let run := evaluate exceptionMoves ct
      run.1 = none ∧ ssaLocalsRel finalNext finalMap st.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel ct run.2 := by
    intro st ct related
    have fixed := fixInconsistenciesCorrectR bodyNext leftMap bodyMap prio st ct
      ⟨allocated,bodyValid⟩
    rw [reconcileProduced] at fixed
    dsimp only at fixed
    exact fixed related
  exact ssa_append_reconciliation_cost TP seqZero
    (evaluate body {setVar name value source with permute := permutation})
    (setVar 2 value target) (.seq retMove (.seq (.move 1 [(renamed,2)]) compiled))
    exceptionMoves bodyMap finalMap bodyNext finalNext tables
    (TP retMove + TP (.move 1 [(renamed,2)]) + bodyEntry retMap retNext +
      wordExecutionCost (fun p _ => SP p) body {setVar name value source with permute := permutation})
    reconciliationWork reconciliationLine moveSpec post

#print axioms ssa_returning_handler_continuation_cost
end InitECandidate.Runtime.FineCost
