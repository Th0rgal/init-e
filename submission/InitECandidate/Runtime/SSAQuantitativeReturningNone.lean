import InitECandidate.Runtime.SSAReturningCostStitch
import InitECandidate.Runtime.SSAReturningOutcomesCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option pp.structureInstances false

/-- Static emitted caller and continuation prefixes for a returning call.
This reads actual compiler output; it does not inspect an execution or use
a program-size bound for the callee or continuation body. -/
noncomputable def ssaReturningLocalPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Nat :=
  match (ssaCcTrans program map next tables).1 with
  | .seq stackMove (.seq argMove (.call (some (regs, names, continuation, l1, l2)) dest args none)) =>
    price stackMove + price argMove + price (.call (some (regs, names, continuation, l1, l2)) dest args none) +
      match continuation with
      | .seq retMove (.seq retCopy _) => price retMove + price retCopy
      | _ => 0
  | _ => 0

theorem ssa_returning_destination_guard (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) :
    wordSemBadDestArgs dest
      ((List.range (args.map (optionLookup ssa)).length).map (fun index => 2*(index+1))) =
      wordSemBadDestArgs dest args := by
  cases args <;> simp [wordSemBadDestArgs]

theorem ssa_returning_convention_distinct (count : Nat) :
    ((List.range count).map (fun index => 2*(index+1))).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro x y equal
  change 2*(x+1) = 2*(y+1) at equal
  omega


/-- Actual returning-call SSA case without a handler: all six original
entry invariants and only the smaller continuation IH. Emitted prefixes,
callee stack transport, selected continuation and root/suffix scheduler work
compose at exact local prices; no callee compiler IH or target run is assumed. -/
theorem ssa_quantitative_returning_none {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (next : Nat)
    (returns : List Nat) (firstNames secondNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (bodyIH : ∀ (st ct : WordSemStateFiniteExact 64 C F) (map : Spt Nat)
      (na : Nat) (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      Flapjack.WordAlloc.wordStateEqRel st ct ∧ ssaLocalsRel na map st.locals ct.locals ∧
      isAllocVar na ∧ everyVarHOL (fun key => decide (key < na)) body = true ∧
      ssaMapOK na map ∧ ltOK lt → SSAQuantitativeSimulation SP TP body st ct map na lt)
    (sourcePrices : ∀ p, TP p ≤ SP p)
    (targetPrices : ∀ p, TP p ≤ wordOptimizerLocalPrice p target)
    (localPrice : ssaReturningLocalPrice TP
      (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) ssa next tables ≤
        SP (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none))
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next))
        (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP
      (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none)
      source target ssa next tables := by
  classical
  obtain ⟨frame,related,allocated,vars,valid,tableValid⟩ := premises
  cases read : WordSemStateFiniteExact.getVars args source with
  | none =>
    refine ⟨source.permute,?_⟩
    simp [WordSemStateFiniteExact.evaluate,read]
  | some values =>
    by_cases bad : wordSemBadDestArgs dest args = true
    · refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad]
    cases found : wordSemFindCode dest (.loc l1 l2 :: values) source.code source.stackSize with
    | none =>
      refine ⟨source.permute,?_⟩
      simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found]
    | some triple =>
      obtain ⟨calleeArgs,callee,size⟩ := triple
      by_cases badCut : sptDomainEmpty firstNames ∨ ¬ returns.Nodup
      · refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut]
      cases cut : wordSemCutEnvs (firstNames,secondNames) source.locals with
      | none =>
        refine ⟨source.permute,?_⟩
        simp [WordSemStateFiniteExact.evaluate,read,bad,wordSemAddRetLoc,found,badCut,cut]
      | some pair =>
        obtain ⟨first,second⟩ := pair
        let names := sptUnion firstNames secondNames
        let nameList := (sptToAList names).map Prod.fst
        have prep := returningPrepareArguments source target ssa next args values firstNames secondNames
          first second cut read related allocated valid frame
        generalize stackProduced : listNextVarRenameMove (width := 64) ssa (next+2) nameList = stackOutput
          at prep
        rcases stackOutput with ⟨stackMove,fresh,counter⟩
        dsimp only at prep
        generalize stackRun : WordSemStateFiniteExact.evaluate stackMove target = firstRun at prep
        rcases firstRun with ⟨firstResult,refreshed⟩
        dsimp only at prep
        obtain ⟨normal,argRun,argRead,newRelated,newFrame,targetFirst,targetSecond,targetCut,
          targetFirstDomain,targetSecondDomain,firstValues,secondValues,firstInjective,secondInjective,
          firstDomain,secondDomain⟩ := prep
        subst firstResult
        let renamedArgs := args.map (optionLookup ssa)
        let convArgs := (List.range renamedArgs.length).map (fun index => 2*(index+1))
        let prepared := WordSemStateFiniteExact.setVars convArgs values refreshed
        generalize moveProduced : listNextVarRenameMove (width := 64) (sptInter fresh names)
          (counter+2) nameList = moveOutput
        rcases moveOutput with ⟨retMove,moveMap,moveNext⟩
        generalize renameProduced : listNextVarRename returns moveMap moveNext = retOutput
        rcases retOutput with ⟨renamed,retMap,retNext⟩
        generalize bodyProduced : ssaCcTrans body retMap retNext tables = bodyOutput
        rcases bodyOutput with ⟨compiled,finalMap,finalNext⟩
        let registers := (List.range returns.length).map (fun index => 2*(index+1))
        let continuation := WordLangProgHOL.seq retMove (.seq (.move 1 (renamed.zip registers)) compiled)
        let targetNames := Flapjack.WordAlloc.applyNummapsKey (optionLookup fresh) (firstNames,secondNames)
        let targetCall := WordLangProgHOL.call (some (registers,targetNames,continuation,l1,l2)) dest convArgs none
        dsimp only [names,nameList] at stackProduced moveProduced
        have compiledWhole : ssaCcTrans
            (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) ssa next tables =
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall),finalMap,finalNext) := by
          simp only [ssaCcTrans,stackProduced,moveProduced,renameProduced,bodyProduced]
          rfl
        have prefixRun : WordSemStateFiniteExact.evaluate
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall)) target =
            WordSemStateFiniteExact.evaluate targetCall prepared := by
          rw [evaluateSeqCollapse _ _ _ _ stackRun,evaluateSeqCollapse _ _ _ _ argRun]
        have properties := listNextVarRenameMoveProps2 nameList ssa next stackMove fresh counter
          stackProduced ⟨Or.inl allocated,valid⟩
        have cutBounds : ∀ key, sptDomain names key → key < counter := by
          have cutVars : (∀ key ∈ (sptToAList firstNames).map Prod.fst, key < next) ∧
              (∀ key ∈ (sptToAList secondNames).map Prod.fst, key < next) := by
            simp only [everyVarHOL,everyNameHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.2
          intro key member
          rw [sptDomain_sptUnion] at member
          have bound := member.elim
            (fun h => cutVars.1 key ((sptMemMapFstToAList _ key).mpr h))
            (fun h => cutVars.2 key ((sptMemMapFstToAList _ key).mpr h))
          omega
        have returnBounds : ∀ key ∈ returns, key < counter := by
          have retVars : ∀ key ∈ returns, key < next := by
            simp only [everyVarHOL,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at vars
            exact vars.2.1.1.1
          intro key member
          have := retVars key member
          omega
        have bodyBounds : everyVarHOL (fun key => decide (key < counter)) body = true := by
          have old : everyVarHOL (fun key => decide (key < next)) body = true := by
            simp only [everyVarHOL,Bool.and_eq_true] at vars
            exact vars.2.1.2
          apply Flapjack.everyVarMono _ body _
          refine ⟨?_,old⟩
          intro key bound
          simp only [decide_eq_true_eq] at bound ⊢
          omega
        have mapped : ∀ key, sptDomain names key → sptDomain fresh key := by
          have subset := cutEnvsDomainSubset firstNames secondNames source.locals (first,second) cut
          intro key member
          rw [sptDomain_sptUnion] at member
          obtain ⟨value,lookup⟩ := (sptMem_iff_lookup key source.locals).mp
            (member.elim (subset.1 key) (subset.2 key))
          exact (newRelated.2 key value lookup).1
        have injection : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
            (sptDomain first b ∨ sptDomain second b) →
            optionLookup fresh a = optionLookup fresh b → a = b := by
          intro a b inA inB equal
          have namedA : sptDomain names a := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inA
          have namedB : sptDomain names b := by
            rw [sptDomain_sptUnion]
            simpa [firstDomain,secondDomain] using inB
          exact listNextVarRenameMoveDistinct ssa (next+2) nameList stackMove fresh counter a b
            ⟨stackProduced,sptAllDistinctMapFstToAList _,(sptMemMapFstToAList _ a).mpr namedA,
              (sptMemMapFstToAList _ b).mpr namedB,equal⟩
        have targetNonempty : ¬ sptDomainEmpty targetNames.1 := by
          change ¬ sptDomainEmpty (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
          intro empty
          have sourceEmpty : sptDomainEmpty firstNames := by
            intro key present
            have namedTarget : sptDomain
                (Flapjack.WordAlloc.applyNummapKey (optionLookup fresh) firstNames)
                (optionLookup fresh key) := by
              rw [Flapjack.WordAlloc.applyNummapKeyDomain]
              exact ⟨key,present,rfl⟩
            exact empty _ namedTarget
          exact (not_or.mp badCut).1 sourceEmpty
        have targetGood : ¬ (sptDomainEmpty targetNames.1 ∨ ¬ registers.Nodup) :=
          not_or.mpr ⟨targetNonempty,not_not.mpr (ssa_returning_convention_distinct _)⟩
        have targetBad : ¬ wordSemBadDestArgs dest convArgs = true := by
          rw [ssa_returning_destination_guard]
          exact bad
        have preparedFrame : Flapjack.WordAlloc.wordStateEqRel source prepared := by
          simpa [prepared,convArgs,renamedArgs] using newFrame
        have preparedRead : WordSemStateFiniteExact.getVars convArgs prepared = some values := by
          simpa [prepared,convArgs,renamedArgs] using argRead
        have preparedCut : wordSemCutEnvs targetNames prepared.locals = some (targetFirst,targetSecond) := by
          simpa [prepared,convArgs,renamedArgs,targetNames] using targetCut
        have fields := preparedFrame
        rcases fields with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
        have targetFound : wordSemFindCode dest
            (wordSemAddRetLoc (some (registers,targetNames,continuation,l1,l2)) values)
            prepared.code prepared.stackSize = some (calleeArgs,callee,size) := by
          simpa [wordSemAddRetLoc,h14,h7] using found
        have firstImage : sptDomain targetFirst =
            (fun key => ∃ name, sptDomain first name ∧ optionLookup fresh name = key) := by
          rw [firstDomain]; exact targetFirstDomain
        have secondImage : sptDomain targetSecond =
            (fun key => ∃ name, sptDomain second name ∧ optionLookup fresh name = key) := by
          rw [secondDomain]; exact targetSecondDomain
        have firstRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain first) first targetFirst := by rw [firstDomain]; exact firstValues
        have secondRelation : Flapjack.WordAlloc.strongLocalsRel (optionLookup fresh)
            (sptDomain second) second targetSecond := by rw [secondDomain]; exact secondValues
        obtain ⟨rootPermutation,roots,stackValues⟩ := Flapjack.WordAlloc.pushEnvSValEq
          (WordSemStateFiniteExact.decClock source) (WordSemStateFiniteExact.decClock prepared)
          second first targetSecond targetFirst (optionLookup fresh) none none
          (wordSemEnvToList targetSecond prepared.permute).2
          ⟨h12.symm,h4.symm,h3.symm,secondImage,secondInjective,firstImage,firstInjective,secondRelation,rfl⟩
        rcases targetRootRead : wordSemEnvToList targetSecond prepared.permute with ⟨targetRoots,targetPerm⟩
        rcases sourceRootRead : wordSemEnvToList second rootPermutation with ⟨sourceRoots,sourcePerm⟩
        have rootFacts := roots
        simp only [WordSemStateFiniteExact.decClock] at rootFacts
        rw [targetRootRead,sourceRootRead] at rootFacts
        dsimp only at rootFacts
        have permutation : (wordSemEnvToList second rootPermutation).2 =
            (wordSemEnvToList targetSecond prepared.permute).2 := by
          rw [sourceRootRead,targetRootRead]
          exact rootFacts.1
        have entry := Flapjack.WordAlloc.calleeSwap preparedFrame first second targetFirst targetSecond
          none none rfl rootPermutation permutation stackValues calleeArgs size
        let sourceBase := {WordSemStateFiniteExact.decClock source with permute := rootPermutation}
        let targetBase := WordSemStateFiniteExact.decClock prepared
        let sourceEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (first,second) none sourceBase)
        let targetEntry := WordSemStateFiniteExact.callEnv calleeArgs size
          (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none targetBase)
        have baseFrame : Flapjack.WordAlloc.wordStateEqRel sourceBase targetBase := by
          simpa [sourceBase,targetBase,WordSemStateFiniteExact.decClock,
            Flapjack.WordAlloc.wordStateEqRel,h13] using preparedFrame
        have localBound : TP stackMove + TP (.move 1 (convArgs.zip renamedArgs)) + TP targetCall +
            (TP retMove + TP (.move 1 (renamed.zip registers))) ≤
            SP (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) := by
          simpa only [ssaReturningLocalPrice, compiledWhole, targetCall, continuation] using localPrice
        have seqZero : ∀ p q, TP (.seq p q) = 0 := by
          intro p q
          have bound := targetPrices (.seq p q)
          change _ ≤ 0 at bound
          omega
        have stackAtomic : wordCostAtomic stackMove = true := by
          have shape := congrArg Prod.fst stackProduced
          simp only [listNextVarRenameMove] at shape
          rw [← shape]
          rfl
        have prefixCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
            (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall)) target =
            TP stackMove + TP (.move 1 (convArgs.zip renamedArgs)) +
              wordExecutionCost (fun p _ => TP p) targetCall prepared := by
          rw [wordExecutionCost_seq, stackRun]
          simp only
          rw [wordExecutionCost_seq, argRun]
          simp only
          rw [wordExecutionCost_atomic _ stackMove _ stackAtomic,
            wordExecutionCost_atomic _ (.move 1 (convArgs.zip renamedArgs)) _ rfl,
            seqZero, seqZero]
          dsimp only [prepared, convArgs, renamedArgs]
          omega
        by_cases zero : source.clock = 0
        · refine ⟨rootPermutation,?_⟩
          have sourceTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout
            {source with permute := rootPermutation} returns (firstNames,secondNames) body l1 l2
            dest args none values calleeArgs callee size (first,second)
            (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
            (by simpa [wordSemAddRetLoc] using found) badCut cut zero
          have targetTimeout := Flapjack.WordAlloc.evaluate_call_ret_timeout prepared registers targetNames
            continuation l1 l2 dest convArgs none values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have maxEqual : (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) none {source with permute := rootPermutation})).stackMax =
              (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (targetFirst,targetSecond) none prepared)).stackMax := by
            simpa only [WordSemStateFiniteExact.decClock,WordSemStateFiniteExact.callEnv,
              WordSemStateFiniteExact.pushEnv] using congrArg WordSemStateFiniteExact.stackMax entry
          dsimp only
          rw [compiledWhole]
          change SSAQuantitativeOutcome finalMap finalNext tables _ _ _ _
          rw [prefixRun, sourceTimeout, targetTimeout]
          right
          refine ⟨rfl, ?_, rfl, ?_⟩
          · simp only [WordSemStateFiniteExact.flushState]
            exact ⟨h1,rfl,rfl,rfl,h5,maxEqual.symm,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21⟩
          · have sourceCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => SP p)
                (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none)
                {source with permute := rootPermutation} =
                SP (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none) := by
              have sourceRead : WordSemStateFiniteExact.getVars args {source with permute := rootPermutation} = some values := by
                rw [WordSemStateFiniteExact.getVars_withPermute]
                exact read
              rw [wordExecutionCost, sourceRead]
              simp only [bad, if_false, Bool.eq_false_iff.mpr bad, Bool.false_eq_true,
                wordSemAddRetLoc, found, if_neg badCut, cut, zero, dite_true]
            have targetCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p) targetCall prepared =
                TP targetCall := by
              simp only [targetCall, wordExecutionCost, preparedRead, targetBad, if_false,
                Bool.eq_false_iff.mpr targetBad, Bool.false_eq_true, wordSemAddRetLoc, targetFound,
                if_neg targetGood, preparedCut, h13, zero, dite_true]
              repeat' split <;> rfl
            rw [prefixCost, sourceCost, targetCost]
            omega
        · have targetRun := Flapjack.WordAlloc.evaluate_call_ret_eq prepared registers targetNames continuation
            l1 l2 dest convArgs none values calleeArgs callee size (targetFirst,targetSecond)
            preparedRead targetBad targetFound targetGood preparedCut (by rw [h13]; exact zero)
          have sourceSuffix : ∀ suffix,
              WordSemStateFiniteExact.evaluate
                (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none)
                {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix} =
              Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none
                (WordSemStateFiniteExact.evaluate callee {sourceEntry with permute := suffix}) := by
            intro suffix
            rw [Flapjack.WordAlloc.evaluate_call_ret_eq
              {source with permute := Flapjack.WordAlloc.ppPerm rootPermutation suffix}
              returns (firstNames,secondNames) body l1 l2 dest args none values calleeArgs callee size
              (first,second) (by rw [WordSemStateFiniteExact.getVars_withPermute]; exact read) bad
              (by simpa [wordSemAddRetLoc] using found) badCut cut zero]
            change Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none
              (WordSemStateFiniteExact.evaluate callee (WordSemStateFiniteExact.callEnv calleeArgs size
                (WordSemStateFiniteExact.pushEnv (first,second) none
                  {WordSemStateFiniteExact.decClock source with permute := (Flapjack.WordAlloc.ppPerm rootPermutation suffix)}))) = _
            rw [Flapjack.WordAlloc.pushEnv_ppPerm]
            rfl
          have outcome := ssa_returning_outcomes_cost SP TP body callee sourceBase targetBase
            (fun p => by rw [← wordOptimizerLocalPrice_state_independent p target targetBase]; exact targetPrices p)
            fresh counter firstNames secondNames first second targetFirst targetSecond calleeArgs size returns l1 l2 tables
            retMove moveMap moveNext renamed retMap retNext compiled finalMap finalNext
            moveProduced renameProduced bodyProduced baseFrame properties.2.2.2 (properties.2.1 allocated)
            firstDomain secondDomain mapped cutBounds returnBounds (not_not.mp (not_or.mp badCut).2) bodyBounds tableValid
            firstRelation injection sourceRoots targetRoots sourcePerm targetPerm sourceRootRead targetRootRead
            rootFacts.2.1 entry stackValues bodyIH
          let targetBody := WordSemStateFiniteExact.evaluate callee targetEntry
          have continuationOutcome : ∃ permutation,
              let sourceBody := ((WordSemStateFiniteExact.evaluate callee sourceEntry).1,
                {(WordSemStateFiniteExact.evaluate callee sourceEntry).2 with permute := permutation})
              SSAQuantitativeOutcome finalMap finalNext tables
                (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none sourceBody)
                (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) none targetBody)
                (TP retMove + TP (.move 1 (renamed.zip registers)) +
                  retCont (fun p _ => SP p) returns body l1 l2 none (first,second) sourceBody.1 sourceBody.2)
                (retCont (fun p _ => TP p) registers continuation l1 l2 none
                  (targetFirst,targetSecond) targetBody.1 targetBody.2) := by
            exact outcome
          obtain ⟨suffix, post⟩ := ssa_returning_cost_stitch SP TP callee sourceEntry targetEntry entry stackValues sourcePrices
            finalMap finalNext tables
            (Flapjack.WordAlloc.callRetTail returns body l1 l2 (first,second) none)
            (Flapjack.WordAlloc.callRetTail registers continuation l1 l2 (targetFirst,targetSecond) none targetBody)
            (fun result => retCont (fun p _ => SP p) returns body l1 l2 none (first,second) result.1 result.2)
            (SP (.call (some (returns,(firstNames,secondNames),body,l1,l2)) dest args none))
            (TP stackMove + TP (.move 1 (convArgs.zip renamedArgs)) + TP targetCall)
            (TP retMove + TP (.move 1 (renamed.zip registers)))
            (retCont (fun p _ => TP p) registers continuation l1 l2 none (targetFirst,targetSecond) targetBody.1 targetBody.2)
            localBound (fun _ => rfl) continuationOutcome
          have targetCallCost := ret_call_cost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
            registers targetNames continuation l1 l2 dest convArgs none prepared values preparedRead
            (Bool.eq_false_iff.mpr targetBad) calleeArgs callee size targetFound targetGood
            (targetFirst,targetSecond) preparedCut (by rw [h13]; exact zero) targetBody.1 targetBody.2 rfl
          have targetCost : wordExecutionCost (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
              (.seq stackMove (.seq (.move 1 (convArgs.zip renamedArgs)) targetCall)) target =
              (TP stackMove + TP (.move 1 (convArgs.zip renamedArgs)) + TP targetCall) +
                wordExecutionCost (fun p _ => TP p) callee targetEntry +
                retCont (fun p _ => TP p) registers continuation l1 l2 none
                  (targetFirst,targetSecond) targetBody.1 targetBody.2 := by
            rw [prefixCost, targetCallCost]
            dsimp only [targetCall, targetEntry, targetBase]
            omega
          have sourceCost := ssa_call_suffix_cost SP returns (firstNames,secondNames) body l1 l2 dest args none
            source rootPermutation suffix values calleeArgs callee size (first,second) read
            (Bool.eq_false_iff.mpr bad) found badCut cut zero
          refine ⟨Flapjack.WordAlloc.ppPerm rootPermutation suffix, ?_⟩
          dsimp only
          rw [compiledWhole]
          change SSAQuantitativeOutcome finalMap finalNext tables _ _ _ _
          rw [prefixRun, targetRun, sourceSuffix, targetCost, sourceCost]
          exact post

#print axioms ssa_quantitative_returning_none
end InitECandidate.Runtime.FineCost
