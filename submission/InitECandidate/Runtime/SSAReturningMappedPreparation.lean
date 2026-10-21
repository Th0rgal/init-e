import InitECandidate.Runtime.WordMoveCodeFrame
import InitECandidate.Runtime.FullSSAMappedReturnFrame
import InitECandidate.Runtime.SSAQuantitativeAllowanceCore
import InitECandidate.Runtime.WordCseAtomicCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Actual saved-cut refresh and return/exception binder over the mapped code
table. This proves both move runs and their exact pure price, deriving the
continuation's locals/map/allocation invariants without a target-run premise. -/
theorem ssa_returning_mapped_preparation {C F : Type}
    (TP : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ a b, TP (.seq a b) = 0)
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat)
    (names : Spt Unit) (counter : Nat) (returns : List Nat) (values : List (WordLocW 64))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext bindNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa names) (counter+2)
      ((sptToAList names).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap bindNext = (renamed,retMap,retNext))
    (bindingIncrease : moveNext ≤ bindNext) (bindingClass : isAllocVar bindNext)
    (related : ssaLocalsRel counter (sptInter ssa names) source.locals target.locals)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (sourceDomain : sptDomain source.locals = sptDomain names)
    (lengths : returns.length = values.length) (distinct : returns.Nodup)
    (below : ∀ name ∈ returns, name < counter) (frame : FullSSATableFrame source target) :
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let program := WordLangProgHOL.seq retMove (.move 1 (renamed.zip registers))
    let prepared := setVars registers values target
    ∃ after refreshedAfter,
      evaluate retMove prepared = (none,refreshedAfter) ∧
      evaluate (.move 1 (renamed.zip registers)) refreshedAfter = (none,after) ∧
      evaluate program prepared = (none,after) ∧
      FullSSATableFrame (setVars returns values source) after ∧
      ssaLocalsRel retNext retMap (setVars returns values source).locals after.locals ∧
      isAllocVar retNext ∧ ssaMapOK retNext retMap ∧ counter ≤ retNext ∧
      wordExecutionCost (fun p _ => TP p) program prepared = TP retMove + TP (.move 1 (renamed.zip registers)) := by
  classical
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let stub := {target with code := source.code}
  let preparedStub := setVars registers values stub
  have allocated := isStackVarFlip counter stackClass
  have nonphysical : ¬ isPhyVar (counter+2) := ((conventionPartitions _).2.2.mp allocated).1
  have restoration := returningRestoreRegistersRead source stub ssa names counter returns.length values
    related valid sourceDomain lengths.symm nonphysical frame.1
  rw [moveProduced] at restoration
  dsimp only at restoration
  rcases run : evaluate retMove preparedStub with ⟨result,refreshed⟩
  change (evaluate retMove preparedStub).1 = none ∧
    ssaLocalsRel moveNext moveMap source.locals (evaluate retMove preparedStub).2.locals ∧
    Flapjack.WordAlloc.wordStateEqRel source (evaluate retMove preparedStub).2 ∧
    getVars registers (evaluate retMove preparedStub).2 = some values at restoration
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
  let bound := setVars renamed values refreshed
  let after := {bound with code := fullSSACodeTable source.code}
  have moveFrame : evaluate retMove {preparedStub with code := fullSSACodeTable source.code} =
      ((evaluate retMove preparedStub).1,{(evaluate retMove preparedStub).2 with code := fullSSACodeTable source.code}) := by
    have shape := congrArg Prod.fst moveProduced
    simp only [listNextVarRenameMove] at shape
    rw [←shape]
    exact word_move_code_frame _ _ _ _
  have inputShape : {preparedStub with code := fullSSACodeTable source.code} = setVars registers values target := by
    simp only [preparedStub,stub,setVars]
    rw [frame.2]
  rw [run,inputShape] at moveFrame
  have copyActual := word_move_code_frame 1 (renamed.zip registers) refreshed (fullSSACodeTable source.code)
  rw [copyRun] at copyActual
  have actual : evaluate (.seq retMove (.move 1 (renamed.zip registers))) (setVars registers values target) =
      (none,after) := by
    rw [evaluateSeqCollapse _ _ _ _ moveFrame]
    exact copyActual
  have afterFrame : FullSSATableFrame (setVars returns values source) after := by
    apply fullSSATableFrame_source_transport _ bound _ copyFrame
    have sameCode : bound.code = source.code := copyFrame.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simpa only [after,sameCode] using fullSSATableFrame_initial bound
  refine ⟨after,{refreshed with code := fullSSACodeTable source.code},moveFrame,copyActual,actual,afterFrame,copyRelated,retProps.2.1 bindingClass,retProps.2.2.2,by omega,?_⟩
  have atomic : wordCostAtomic retMove = true := by
    have shape := congrArg Prod.fst moveProduced
    simp only [listNextVarRenameMove] at shape
    rw [←shape]
    rfl
  rw [wordExecutionCost_seq,moveFrame]
  simp only [seqZero,Nat.zero_add]
  rw [wordExecutionCost_atomic _ retMove _ atomic,
    wordExecutionCost_atomic _ (.move 1 (renamed.zip registers)) _ rfl]

#print axioms ssa_returning_mapped_preparation
end InitECandidate.Runtime.FineCost
