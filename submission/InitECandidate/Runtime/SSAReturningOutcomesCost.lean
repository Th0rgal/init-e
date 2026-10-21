import InitECandidate.Runtime.SSAReturningSuccessCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- All actual callee outcomes of a returning call without a handler. Invalid
returns retain source-error exemption; accepted returns derive frame restoration
and exact continuation work; terminal/escaping outcomes pay no continuation.
No desired target run, continuation post-relation or callee IH is assumed. -/
theorem ssa_returning_outcomes_cost {C F : Type}
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
      ssaMapOK retNext retMap ∧ ltOK tables → SSAQuantitativeAllowance SP TP body st ct retMap retNext tables (bodyEntry retMap retNext)) :
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
  rcases sourceRun : WordSemStateFiniteExact.evaluate callee sourceEntry with ⟨result,returned⟩
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
  cases result with
  | none => exact ⟨returned.permute, by simp [Flapjack.WordAlloc.callRetTail]⟩
  | some result =>
    cases result with
    | error => exact ⟨returned.permute, by simp [Flapjack.WordAlloc.callRetTail]⟩
    | «break» n => exact ⟨returned.permute, by simp [Flapjack.WordAlloc.callRetTail]⟩
    | «continue» n => exact ⟨returned.permute, by simp [Flapjack.WordAlloc.callRetTail]⟩
    | timeOut =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute, ?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail, SSAResultLocals, Flapjack.WordAlloc.wordStateEqRel, retCont]
    | notEnoughSpace =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute, ?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail, SSAResultLocals, Flapjack.WordAlloc.wordStateEqRel, retCont]
    | finalFfi event =>
      have actual := targetTransport _ (transport.2.2 _ stackValues)
      refine ⟨returned.permute, ?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail, SSAResultLocals, Flapjack.WordAlloc.wordStateEqRel, retCont]
    | exception x y =>
      have sourceShape : sourceEntry.stack =
          .stackFrame source.localsSize (sptToAList first) sourceRoots none :: source.stack := by
        simp only [sourceEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, sourceRootRead]
      have targetShape : targetEntry.stack =
          .stackFrame target.localsSize (sptToAList targetFirst) targetRoots none :: source.stack := by
        simp only [targetEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, targetRootRead]
        rw [sameStack]
      have actual := returningNoHandlerException callee sourceEntry targetEntry returned source.stack
        source.localsSize target.localsSize (sptToAList first) sourceRoots (sptToAList targetFirst)
        targetRoots x y sourceShape targetShape entry stackValues sourceRun
      refine ⟨returned.permute, ?_⟩
      rw [actual]
      simp [Flapjack.WordAlloc.callRetTail, SSAResultLocals, Flapjack.WordAlloc.wordStateEqRel, retCont]
    | result x values =>
      by_cases badReturn : x ≠ .loc l1 l2 ∨ values.length ≠ returns.length
      · refine ⟨returned.permute, ?_⟩
        rw [Flapjack.WordAlloc.callRetTail_result_err _ _ _ _ _ _ _ _ _ badReturn]
        exact Or.inl rfl
      · have success := ssa_returning_success_cost SP TP bodyEntry body callee source target targetPrices ssa counter
          firstNames secondNames first second targetFirst targetSecond args size returns l1 l2 tables
          retMove moveMap moveNext renamed retMap retNext compiled finalMap finalNext
          moveProduced renameProduced bodyProduced frame valid stackClass firstDomain secondDomain mapped cutBounds
          below distinct bodyBounds tableValid firstRelated injective sourceRoots targetRoots sourcePerm targetPerm
          sourceRootRead targetRootRead rootMap entry stackValues bodyIH x values returned sourceRun badReturn
        simpa only [sourceEntry, targetEntry, registers, continuation, sourceRun] using success

#print axioms ssa_returning_outcomes_cost
end InitECandidate.Runtime.FineCost
