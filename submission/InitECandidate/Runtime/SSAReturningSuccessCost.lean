import InitECandidate.Runtime.SSAReturningContinuationCost
import InitECandidate.Runtime.WordCallExecutionCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Successful actual callee return: derive target callee execution, frame
pop, saved-cut SSA relation and emitted continuation execution from the original
root/cut/compiler invariants. Exact restoration/binder prices are retained.
Only the smaller continuation-body IH is used; no target run is assumed. -/
theorem ssa_returning_success_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (bodyEntry : Spt Nat → Nat → Nat)
    (body callee : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (ssa : Spt Nat) (counter : Nat) (firstNames secondNames : Spt Unit)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (args : List (WordLocW 64)) (size : Option Nat)
    (returns : List Nat) (l1 l2 : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (finalMap : Spt Nat) (finalNext : Nat)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa (sptUnion firstNames secondNames))
      (counter+2) ((sptToAList (sptUnion firstNames secondNames)).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,finalMap,finalNext))
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (valid : ssaMapOK counter ssa) (stackClass : isStackVar counter)
    (firstDomain : sptDomain first = sptDomain firstNames)
    (secondDomain : sptDomain second = sptDomain secondNames)
    (mapped : ∀ key, sptDomain (sptUnion firstNames secondNames) key → sptDomain ssa key)
    (cutBounds : ∀ key, sptDomain (sptUnion firstNames secondNames) key → key < counter)
    (below : ∀ name ∈ returns, name < counter) (distinct : returns.Nodup)
    (bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true)
    (tableValid : ltOK tables)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → optionLookup ssa a = optionLookup ssa b → a = b)
    (sourceRoots targetRoots : List (Nat × WordLocW 64)) (sourcePerm targetPerm : Nat → Nat → Nat)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots,sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots,targetPerm))
    (rootMap : sourceRoots.map (fun (key,value) => (optionLookup ssa key,value)) = targetRoots)
    (entry : {WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (first,second) none source) with stack :=
        (WordSemStateFiniteExact.callEnv args size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target)).stack} =
      WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target))
    (stackValues : WordSemStackEq.sValEq
      (WordSemStateFiniteExact.pushEnv (first,second) none source).stack
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target).stack)
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel retNext retMap st.locals ct.locals ∧
      isAllocVar retNext ∧ everyVarHOL (fun key => decide (key < retNext)) body = true ∧
      ssaMapOK retNext retMap ∧ ltOK tables → SSAQuantitativeAllowance SP TP body st ct retMap retNext tables (bodyEntry retMap retNext))
    (x : WordLocW 64) (values : List (WordLocW 64)) (returned : WordSemStateFiniteExact 64 C F)
    (sourceRun : evaluate callee (callEnv args size (pushEnv (first,second) none source)) =
      (some (.result x values), returned))
    (badReturn : ¬ (x ≠ .loc l1 l2 ∨ values.length ≠ returns.length)) :
    let sourceEntry := callEnv args size (pushEnv (first,second) none source)
    let targetEntry := callEnv args size (pushEnv (targetFirst,targetSecond) none target)
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
    ∃ permutation : Nat → Nat → Nat,
      let sourceBody := ((evaluate callee sourceEntry).1, {(evaluate callee sourceEntry).2 with permute := permutation})
      let targetBody := evaluate callee targetEntry
      let sourceFinal := Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none sourceBody
      let targetFinal := Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) none targetBody
      sourceFinal.1 = some .error ∨ sourceFinal.1 = targetFinal.1 ∧
        Flapjack.WordAlloc.wordStateEqRel sourceFinal.2 targetFinal.2 ∧
        SSAResultLocals finalNext finalMap tables sourceFinal.2.locals targetFinal.2.locals sourceFinal.1 ∧
        retCont (fun p _ => TP p) registers continuation l1 l2 none (targetFirst,targetSecond) targetBody.1 targetBody.2 ≤
          TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext +
            retCont (fun p _ => SP p) returns body l1 l2 none (first,second) sourceBody.1 sourceBody.2 := by
  let sourceEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (first,second) none source)
  let targetEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none target)
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
  have transport := WordSemStackEq.evaluateStackSwap callee sourceEntry
  unfold WordSemStackEq.stackSwapPost at transport
  rw [sourceRun] at transport
  dsimp only
  rw [sourceRun]
  dsimp only
  have targetTransport : ∀ result,
      WordSemStateFiniteExact.evaluate callee {sourceEntry with stack := targetEntry.stack} = result →
      WordSemStateFiniteExact.evaluate callee targetEntry = result := by
    intro result run
    rw [entry] at run
    exact run
  have sameStack : source.stack = target.stack := frame.2.2.2.1.symm
  have targetGood : ¬ (x ≠ .loc l1 l2 ∨ values.length ≠ registers.length) := by
    simpa [registers] using badReturn
  obtain ⟨sourceKeys,_,swapped⟩ := transport
  obtain ⟨targetStack,swappedRun,valuesEqual,targetKeys⟩ := swapped targetEntry.stack stackValues
  have actual := targetTransport _ swappedRun
  obtain ⟨popped,targetPopped,sourcePop,targetPop,poppedFrame,poppedDomain,poppedValues⟩ :=
    returningPopCutRelation source target returned first second targetFirst targetSecond none none
      targetStack (optionLookup ssa) sourceRoots targetRoots sourcePerm targetPerm sameStack
      sourceRootRead targetRootRead rootMap firstRelated injective sourceKeys targetKeys valuesEqual
  have sourceNames : sptDomain popped.locals = sptDomain (sptUnion firstNames secondNames) := by
    rw [poppedDomain,sptDomain_sptUnion,firstDomain,secondDomain]
  have restricted := returningCutSSA counter ssa (sptUnion firstNames secondNames)
    popped.locals targetPopped.locals mapped sourceNames (poppedValues _) cutBounds
  have sourceUnion : sptDomainEqUnion popped.locals first second := by
    intro key
    change sptDomain popped.locals key ↔ sptDomain first key ∨ sptDomain second key
    have equality := congrFun poppedDomain key
    rw [equality]
  obtain ⟨_,_,_,_,_,otherPop,otherPopRun,_,targetDomain,_⟩ :=
    WordSemStackEq.pushEnvPopEnvSKeyEq (targetFirst,targetSecond) none target
      {returned with stack := targetStack} targetKeys
  have samePop : otherPop = targetPopped := by
    rw [targetPop] at otherPopRun
    exact Option.some.inj otherPopRun.symm
  rw [samePop] at targetDomain
  have targetUnion : sptDomainEqUnion targetPopped.locals targetFirst targetSecond := by
    intro key
    change sptDomain targetPopped.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
    have equality := congrFun targetDomain key
    rw [←equality]
    exact Or.comm
  have lengths : returns.length = values.length := by
    have := (not_or.mp badReturn).2
    omega
  have allocated := isStackVarFlip counter stackClass
  have moveProps := listNextVarRenameMoveProps _ (sptInter ssa (sptUnion firstNames secondNames)) (counter+2)
    retMove moveMap moveNext moveProduced
    ⟨Or.inl allocated, ssaMapOKMore counter _ (counter+2)
      ⟨ssaMapOKInter counter ssa _ valid, by omega⟩⟩
  have targetPrices' : ∀ p, TP p ≤ wordOptimizerLocalPrice p targetPopped := by
    intro p
    rw [← wordOptimizerLocalPrice_state_independent p target targetPopped]
    exact targetPrices p
  obtain ⟨permutation, post⟩ := ssa_returning_general_continuation_entry SP TP bodyEntry body popped targetPopped ssa targetPrices'
    (sptUnion firstNames secondNames) counter returns values tables retMove moveMap moveNext moveNext
    renamed retMap retNext compiled finalMap finalNext moveProduced renameProduced bodyProduced
    (Nat.le_refl _) (moveProps.2.1 allocated) restricted valid stackClass sourceNames lengths distinct below
    bodyBounds poppedFrame tableValid bodyIH
  refine ⟨permutation, ?_⟩
  rw [actual,
    Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ {popped with permute := permutation}
      badReturn (by rw [Flapjack.WordAlloc.popEnv_withPermute,sourcePop]; rfl),
    Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ targetPopped targetGood targetPop]
  rw [if_pos sourceUnion,if_pos targetUnion]
  have sourcePopPerm : popEnv {returned with permute := permutation} =
      some {popped with permute := permutation} := by
    rw [Flapjack.WordAlloc.popEnv_withPermute, sourcePop]
    rfl
  simp only [retCont, if_neg badReturn, if_neg targetGood, sourcePopPerm, targetPop,
    if_pos sourceUnion, if_pos targetUnion]
  have sourceShape : setVars returns values {popped with permute := permutation} =
      {setVars returns values popped with permute := permutation} := rfl
  rw [sourceShape]
  simpa only [registers, List.length_map, List.length_range, if_neg badReturn] using post


#print axioms ssa_returning_success_cost
end InitECandidate.Runtime.FineCost
