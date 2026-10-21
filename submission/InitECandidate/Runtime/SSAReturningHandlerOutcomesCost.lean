import InitECandidate.Runtime.SSAReturningHandlerContinuationCost
import InitECandidate.Runtime.SSAReturningHandlerExceptionCost
import InitECandidate.Runtime.SSAReturningSuccessCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- All actual callee outcomes with a compiled handler. Normal and exception
continuations retain their actual refresh, binder, body-entry and reconciliation
prices; only the larger selected-branch budget is charged. No desired target
run or restored frame is assumed. -/
theorem ssa_returning_handler_outcomes_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (bodyEntry handlerEntry : Spt Nat → Nat → Nat)
    (prices : ∀ p, TP p ≤ SP p) (seqZero : ∀ a b, TP (.seq a b) = 0)
    (body handlerBody callee : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (ssa : Spt Nat) (counter : Nat) (firstNames secondNames : Spt Unit)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (args : List (WordLocW 64)) (size : Option Nat)
    (returns : List Nat) (l1 l2 exceptionVar handlerL1 handlerL2 : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (retMove : WordLangProgHOL (BitVec 64)) (moveMap : Spt Nat) (moveNext : Nat)
    (renamed : List Nat) (retMap : Spt Nat) (retNext : Nat)
    (compiled : WordLangProgHOL (BitVec 64)) (leftMap : Spt Nat) (leftNext : Nat)
    (exceptionOut : Nat) (exceptionMap : Spt Nat) (exceptionNext : Nat)
    (compiledException : WordLangProgHOL (BitVec 64)) (rightMap : Spt Nat) (rightNext : Nat)
    (prio : Option (Unit ⊕ Unit)) (retCons excCons : WordLangProgHOL (BitVec 64))
    (finalMap : Spt Nat) (finalNext : Nat)
    (exceptionProduced : nextVarRename exceptionVar moveMap leftNext =
      (exceptionOut,exceptionMap,exceptionNext))
    (handlerProduced : ssaCcTrans handlerBody exceptionMap exceptionNext tables =
      (compiledException,rightMap,rightNext))
    (reconcileProduced : fixInconsistencies prio leftMap rightMap rightNext =
      (retCons,excCons,finalNext,finalMap))
    (leftAllocated : isAllocVar leftNext) (rightAllocated : isAllocVar rightNext)
    (leftValid : ssaMapOK leftNext leftMap) (rightValid : ssaMapOK rightNext rightMap)
    (moveIncrease : moveNext ≤ leftNext) (leftIncrease : leftNext ≤ rightNext)
    (exceptionBelow : exceptionVar < counter)
    (handlerBounds : everyVarHOL (fun key => decide (key < counter)) handlerBody = true)
    (moveProduced : listNextVarRenameMove (width := 64) (sptInter ssa (sptUnion firstNames secondNames))
      (counter+2) ((sptToAList (sptUnion firstNames secondNames)).map Prod.fst) = (retMove,moveMap,moveNext))
    (renameProduced : listNextVarRename returns moveMap moveNext = (renamed,retMap,retNext))
    (bodyProduced : ssaCcTrans body retMap retNext tables = (compiled,leftMap,leftNext))
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
        (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source) with stack :=
        (WordSemStateFiniteExact.callEnv args size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)).stack} =
      WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target))
    (stackValues : WordSemStackEq.sValEq
      (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source).stack
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target).stack)
    (normalWork exceptionWork : Nat)
    (normalLine : lineBound (ssaReconciliationLeaf TP) retCons = some normalWork)
    (exceptionLine : lineBound (ssaReconciliationLeaf TP) excCons = some exceptionWork)
    (handlerIH : SSABodyAllowance (C := C) (F := F) SP TP handlerBody exceptionMap exceptionNext tables
      (handlerEntry exceptionMap exceptionNext))
    (bodyIH : SSABodyAllowance (C := C) (F := F) SP TP body retMap retNext tables
      (bodyEntry retMap retNext)) :
    let sourceEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source)
    let targetEntry := WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)
    let registers := (List.range returns.length).map (fun index => 2*(index+1))
    let retBody := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
    let continuation := WordLangProgHOL.seq retBody retCons
    let exceptionBody := WordLangProgHOL.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)
    let exceptionContinuation := WordLangProgHOL.seq exceptionBody excCons
    ∃ permutation : Nat → Nat → Nat,
      SSAQuantitativeOutcome finalMap finalNext tables
        (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2))
          ((WordSemStateFiniteExact.evaluate callee sourceEntry).1,
            {(WordSemStateFiniteExact.evaluate callee sourceEntry).2 with permute := permutation}))
        (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) (some (2,exceptionContinuation,handlerL1,handlerL2))
          (WordSemStateFiniteExact.evaluate callee targetEntry))
        (max (TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext + normalWork)
          (TP retMove + TP (.move 1 [(exceptionOut,2)]) + handlerEntry exceptionMap exceptionNext + exceptionWork) +
          retCont (fun p _ => SP p) returns body l1 l2 (some (exceptionVar,handlerBody,handlerL1,handlerL2))
            (first,second) (evaluate callee sourceEntry).1
            {(evaluate callee sourceEntry).2 with permute := permutation})
        (retCont (fun p _ => TP p) registers continuation l1 l2 (some (2,exceptionContinuation,handlerL1,handlerL2))
          (targetFirst,targetSecond) (evaluate callee targetEntry).1 (evaluate callee targetEntry).2) := by
  let sourceEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (first,second) (some (exceptionVar,handlerBody,handlerL1,handlerL2)) source)
  let targetEntry := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target)
  let registers := (List.range returns.length).map (fun index => 2*(index+1))
  let retBody := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
  let continuation := WordLangProgHOL.seq retBody retCons
  let exceptionBody := WordLangProgHOL.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)
  let exceptionContinuation := WordLangProgHOL.seq exceptionBody excCons
  have normalReconcile : ∀ (st ct : WordSemStateFiniteExact 64 C F),
      ssaLocalsRel leftNext leftMap st.locals ct.locals →
      let run := WordSemStateFiniteExact.evaluate retCons ct
      run.1 = none ∧ ssaLocalsRel finalNext finalMap st.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel ct run.2 := by
    intro st ct related
    have fixed := fixInconsistenciesCorrectL rightNext leftMap rightMap prio st ct
      ⟨rightAllocated,ssaMapOKMore leftNext leftMap rightNext ⟨leftValid,leftIncrease⟩⟩
    rw [reconcileProduced] at fixed
    dsimp only at fixed
    exact fixed (ssaLocalsRelMore leftNext leftMap st.locals ct.locals rightNext ⟨related,leftIncrease⟩)
  have transport := WordSemStackEq.evaluateStackSwap callee sourceEntry
  unfold WordSemStackEq.stackSwapPost at transport
  rcases sourceRun : WordSemStateFiniteExact.evaluate callee sourceEntry with ⟨result,returned⟩
  rw [sourceRun] at transport
  dsimp only
  rw [sourceRun]
  dsimp only
  unfold SSAQuantitativeOutcome
  have targetTransport : ∀ result,
      WordSemStateFiniteExact.evaluate callee {sourceEntry with stack := targetEntry.stack} = result →
      WordSemStateFiniteExact.evaluate callee targetEntry = result := by
    intro result run
    rw [entry] at run
    exact run
  have sameStack : source.stack = target.stack := frame.2.2.2.1.symm
  cases result with
  | none => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont]⟩
  | some result =>
    cases result with
    | error => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont]⟩
    | «break» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont]⟩
    | «continue» n => exact ⟨returned.permute,by simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont]⟩
    | timeOut =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont,Flapjack.WordAlloc.wordStateEqRel]
    | notEnoughSpace =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont,Flapjack.WordAlloc.wordStateEqRel]
    | finalFfi event =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute,?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail,SSAResultLocals, retCont,Flapjack.WordAlloc.wordStateEqRel]
    | exception x y =>
      by_cases badLabel : x ≠ .loc handlerL1 handlerL2
      · refine ⟨returned.permute,?_⟩
        simp [Flapjack.WordAlloc.callRetTail,badLabel,SSAResultLocals, retCont]
      have sourceShape : sourceEntry.stack = .stackFrame source.localsSize (sptToAList first) sourceRoots
          (some (source.handler,handlerL1,handlerL2)) :: source.stack := by
        simp only [sourceEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,sourceRootRead]
      have targetShape : targetEntry.stack = .stackFrame source.localsSize (sptToAList targetFirst) targetRoots
          (some (source.handler,handlerL1,handlerL2)) :: source.stack := by
        simp only [targetEntry,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,targetRootRead]
        rw [frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.2.2.2.2.2.2.2.1]
      have sourceRootKeys : ∀ key, key ∈ sourceRoots.map Prod.fst ↔ sptDomain second key := by
        have equality := Flapjack.WordAlloc.envToListKeys second source.permute
        rw [sourceRootRead] at equality
        intro key
        exact (congrFun equality key).to_iff
      have targetRootKeys : ∀ key, key ∈ targetRoots.map Prod.fst ↔ sptDomain targetSecond key := by
        have equality := Flapjack.WordAlloc.envToListKeys targetSecond target.permute
        rw [targetRootRead] at equality
        intro key
        exact (congrFun equality key).to_iff
      obtain ⟨targetReturned,actual,returnedFrame,returnedDomain,targetDomain,returnedValues,calleeCost⟩ :=
        ssa_returning_handler_exception_cost SP TP prices callee sourceEntry targetEntry returned source.stack source.localsSize
          first second targetFirst targetSecond sourceRoots targetRoots source.handler handlerL1 handlerL2 x y
          (optionLookup ssa) sourceShape targetShape (by rfl) entry stackValues sourceRootKeys targetRootKeys
          rootMap firstRelated injective sourceRun
      have sourceNames : sptDomain returned.locals = sptDomain (sptUnion firstNames secondNames) := by
        rw [returnedDomain,sptDomain_sptUnion,firstDomain,secondDomain]
      have restricted := returningCutSSA counter ssa (sptUnion firstNames secondNames)
        returned.locals targetReturned.locals mapped sourceNames (returnedValues _) cutBounds
      have sourceUnion : sptDomainEqUnion returned.locals first second := by
        intro key
        change sptDomain returned.locals key ↔ sptDomain first key ∨ sptDomain second key
        rw [congrFun returnedDomain key]
      have targetUnion : sptDomainEqUnion targetReturned.locals targetFirst targetSecond := by
        intro key
        change sptDomain targetReturned.locals key ↔ sptDomain targetFirst key ∨ sptDomain targetSecond key
        rw [congrFun targetDomain key]
      have targetPrices' : ∀ p, TP p ≤ wordOptimizerLocalPrice p targetReturned := by
        intro p
        rw [←wordOptimizerLocalPrice_state_independent p target targetReturned]
        exact targetPrices p
      obtain ⟨permutation,composed⟩ := ssa_returning_handler_continuation_cost SP TP handlerEntry
        handlerBody returned targetReturned ssa targetPrices' (sptUnion firstNames secondNames)
        counter exceptionVar y tables retMove moveMap moveNext leftNext exceptionOut exceptionMap exceptionNext
        compiledException rightMap rightNext moveProduced exceptionProduced handlerProduced moveIncrease
        leftAllocated restricted valid stackClass sourceNames exceptionBelow handlerBounds returnedFrame
        tableValid seqZero leftMap finalMap finalNext prio retCons excCons reconcileProduced rightAllocated
        rightValid exceptionWork exceptionLine handlerIH
      refine ⟨permutation,?_⟩
      rw [actual]
      simp only [Flapjack.WordAlloc.callRetTail,if_neg badLabel,if_pos sourceUnion,if_pos targetUnion,
        retCont]
      change SSAQuantitativeOutcome finalMap finalNext tables _ _ _ _ at composed
      rcases composed with error | ⟨same,postFrame,postLocals,cost⟩
      · exact Or.inl error
      · right
        refine ⟨same,postFrame,postLocals,?_⟩
        have budget := Nat.le_max_right
          (TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext + normalWork)
          (TP retMove + TP (.move 1 [(exceptionOut,2)]) + handlerEntry exceptionMap exceptionNext + exceptionWork)
        change wordExecutionCost (fun p _ => TP p) exceptionContinuation (setVar 2 y targetReturned) ≤ _ at cost
        dsimp only [exceptionContinuation,exceptionBody] at cost
        simp only [setVar] at cost ⊢
        dsimp only [registers] at budget
        apply Nat.le_trans cost
        omega
    | result x values =>
      by_cases badReturn : x ≠ .loc l1 l2 ∨ values.length ≠ returns.length
      · refine ⟨returned.permute,?_⟩
        rw [Flapjack.WordAlloc.callRetTail_result_err _ _ _ _ _ _ _ _ _ badReturn]
        simp [SSAResultLocals, retCont]
      have targetGood : ¬ (x ≠ .loc l1 l2 ∨ values.length ≠ registers.length) := by
        simpa [registers] using badReturn
      obtain ⟨sourceKeys,_,swapped⟩ := transport
      obtain ⟨targetStack,swappedRun,valuesEqual,targetKeys⟩ := swapped targetEntry.stack stackValues
      have actual := targetTransport _ swappedRun
      obtain ⟨popped,targetPopped,sourcePop,targetPop,poppedFrame,poppedDomain,poppedValues⟩ :=
        returningPopCutRelation source target returned first second targetFirst targetSecond (some (exceptionVar,handlerBody,handlerL1,handlerL2)) (some (2,exceptionContinuation,handlerL1,handlerL2))
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
        WordSemStackEq.pushEnvPopEnvSKeyEq (targetFirst,targetSecond) (some (2,(.seq (.seq retMove (.seq (.move 1 [(exceptionOut,2)]) compiledException)) excCons),handlerL1,handlerL2)) target
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
        rw [←wordOptimizerLocalPrice_state_independent p target targetPopped]
        exact targetPrices p
      obtain ⟨permutation,post⟩ := ssa_returning_general_continuation_entry SP TP bodyEntry
        body popped targetPopped ssa targetPrices' (sptUnion firstNames secondNames) counter returns values tables
        retMove moveMap moveNext moveNext renamed retMap retNext compiled leftMap leftNext
        moveProduced renameProduced bodyProduced (Nat.le_refl _) (moveProps.2.1 allocated)
        restricted valid stackClass sourceNames lengths distinct below bodyBounds poppedFrame tableValid bodyIH
      have composed := ssa_append_reconciliation_cost TP seqZero
        (evaluate body {setVars returns values popped with permute := permutation})
        (setVars registers values targetPopped) retBody retCons leftMap finalMap leftNext finalNext tables
        (TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext +
          wordExecutionCost (fun p _ => SP p) body {setVars returns values popped with permute := permutation})
        normalWork normalLine normalReconcile post
      refine ⟨permutation,?_⟩
      rw [actual,
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ {popped with permute := permutation}
          badReturn (by rw [Flapjack.WordAlloc.popEnv_withPermute,sourcePop]; rfl),
        Flapjack.WordAlloc.callRetTail_result_pop _ _ _ _ _ _ _ _ _ targetPopped targetGood targetPop]
      rw [if_pos sourceUnion,if_pos targetUnion]
      have sourcePopPerm : popEnv {returned with permute := permutation} =
          some {popped with permute := permutation} := by
        rw [Flapjack.WordAlloc.popEnv_withPermute,sourcePop]
        rfl
      simp only [retCont,if_neg badReturn,if_neg targetGood,sourcePopPerm,targetPop,
        if_pos sourceUnion,if_pos targetUnion, List.length_map, List.length_range, if_neg badReturn]
      rcases composed with error | ⟨same,postFrame,postLocals,cost⟩
      · exact Or.inl error
      · right
        refine ⟨same,postFrame,postLocals,?_⟩
        have budget := Nat.le_max_left
          (TP retMove + TP (.move 1 (renamed.zip registers)) + bodyEntry retMap retNext + normalWork)
          (TP retMove + TP (.move 1 [(exceptionOut,2)]) + handlerEntry exceptionMap exceptionNext + exceptionWork)
        have sourceShape : setVars returns values {popped with permute := permutation} =
            {setVars returns values popped with permute := permutation} := rfl
        rw [sourceShape]
        dsimp only [registers] at budget cost ⊢
        apply Nat.le_trans cost
        omega

#print axioms ssa_returning_handler_outcomes_cost
end InitECandidate.Runtime.FineCost
