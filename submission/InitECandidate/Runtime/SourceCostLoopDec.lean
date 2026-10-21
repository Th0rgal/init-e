import InitECandidate.Runtime.SourceCostLoopTransfer
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Dec
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Declaration transfer: the pinned Dec-case relation reasoning, with the
initializer code, the slot assignment and the body charged on the actual
Loop run. -/
theorem dec_loop_paid (P : LoopPricing) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F} {name : Nat}
    {e : CrepExpHOL 64} {body : CrepProgHOL 64} {value : HolWordLab 64} {bodyWork : Nat}
    (evaluated : evalCrepSemHOLExp v1 e = some value)
    (ok : (evalCrepSemHOLProgExact v1 (.dec name e body)).1 ≠ some .error)
    (rel : CrepLoopRel ctxt l v1 t)
    (ih : ∀ (u' : LoopSemStateFiniteExact 64 F) (ctxt' : CrepToLoopContextExact) (live' : NumSet),
      (evalCrepSemHOLProgExact { v1 with locals := v1.locals.updateEq (name, value) } body).1 ≠
        some .error →
      CrepLoopRel ctxt' live' { v1 with locals := v1.locals.updateEq (name, value) } u' →
      LoopPaid ctxt' live' { v1 with locals := v1.locals.updateEq (name, value) } u' body
        bodyWork) :
    LoopPaid ctxt l v1 t (.dec name e body) (P.price e + bodyWork) := by
  have unitOk := P.unitOk
  classical
  rcases hEvalAll : evalCrepSemHOLProgExact v1 (.dec name e body) with ⟨res, s1⟩
  have he := hEvalAll
  have hne : res ≠ some .error := by rw [hEvalAll] at ok; exact ok
  obtain ⟨hs, hm, hg, hc, hl⟩ := rel
  rw [evalCrepSemHOLProgExact_dec_holShape] at he
  have hev := evaluated
  simp only [hev] at he
  let sourceBody : CrepSemHOLState 64 F :=
    { v1 with locals := v1.locals.updateEq (name, value) }
  cases hBody : evalCrepSemHOLProgExact sourceBody body with
  | mk bodyResult bodyState =>
    rw [hBody] at he
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨hResult, hFinal⟩
    have hBodyEval : evalCrepSemHOLProgExact sourceBody body = (bodyResult, bodyState) := hBody
    rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with
      ⟨codePrefix, compiledValue, temporary, nextLive⟩
    obtain ⟨prefixClock, prefixState, hPrefix, hValue, hPrefixState,
      hPrefixMem, hPrefixGlobals, hPrefixCode, hPrefixLocals⟩ :=
      crepToLoop_comp_exp_preserves_eval v1 e value t ctxt (ctxt.vmax + 1) l
        codePrefix compiledValue temporary nextLive
        ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
    obtain ⟨hNoContext, hTempBound, hNextLive⟩ :=
      compile_exp_out_rel ctxt (ctxt.vmax + 1) l e codePrefix compiledValue temporary nextLive hC
    have hLiveNext : ∀ k, sptMem k l → sptMem k nextLive := by
      intro k hk
      rw [hNextLive]
      exact cut_sets_union_domain_subset _ l hNoContext k hk
    have hLocalsBefore : crepToLoopLocalsRelExact ctxt l v1.locals prefixState.locals := by
      refine ⟨hPrefixLocals.1, hPrefixLocals.2.1, ?_, ?_⟩
      intro k hk
      exact hPrefixLocals.2.2.1 k (hLiveNext k hk)
      intro key val hval
      obtain ⟨n, hmap, hmem, _⟩ := hl.2.2.2 key val hval
      obtain ⟨n', hmap', _, hslot⟩ := hPrefixLocals.2.2.2 key val hval
      have hn : n' = n := Option.some.inj (hmap'.symm.trans hmap)
      subst n'
      exact ⟨n, hmap', hmem, hslot⟩
    have hFresh : ctxt.vmax < temporary := by omega
    let bodyCtxt : CrepToLoopContextExact :=
      { ctxt with vars := ctxt.vars.updateEq (name, temporary), vmax := temporary }
    let bodyLive : NumSet := sptInsert temporary () l
    let targetBody : LoopSemStateFiniteExact 64 F :=
      LoopSemStateFiniteExact.setVar temporary (wlabWlocExact value) prefixState
    have hBodyLocals : crepToLoopLocalsRelExact bodyCtxt bodyLive
        sourceBody.locals targetBody.locals := by
      have hw : (wlabWlocExact : HolWordLab 64 → WordLocW 64) = wlabWlocHOL := by
        funext v
        cases v
        rfl
      have hEntered := crepToLoopNcompileDecLocalsEnter ctxt l v1.locals prefixState.locals
        name temporary value hLocalsBefore hFresh
      rw [← hw] at hEntered
      simpa [sourceBody, targetBody, bodyLive, bodyCtxt, CrepSemHOLState.setVar,
        LoopSemStateFiniteExact.setVar] using hEntered
    have hBodyState : crepToLoopStateRelExact sourceBody targetBody := by
      simpa [sourceBody, targetBody, crepToLoopStateRelExact,
        LoopSemStateFiniteExact.setVar] using hPrefixState
    have hBodyMem : crepToLoopMemRelHOLExact sourceBody.memory targetBody.memory
        sourceBody.memaddrs := by
      simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixMem
    have hBodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals targetBody.globals := by
      simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixGlobals
    have hBodyCode : crepToLoopCodeRelExact bodyCtxt sourceBody.code targetBody.code := by
      simpa [sourceBody, targetBody, bodyCtxt, crepToLoopCodeRelExact,
        LoopSemStateFiniteExact.setVar] using hPrefixCode
    have hBodyNotError : bodyResult ≠ some .error := by
      intro herr
      apply hne
      rw [← hResult]
      exact herr
    obtain ⟨bodyClock, bodyWl, bodyWorkDeriv, bodyWlBound, bodyRel⟩ :=
      ih targetBody bodyCtxt bodyLive (by rw [hBodyEval]; exact hBodyNotError)
        ⟨hBodyState, hBodyMem, hBodyGlobals, hBodyCode, hBodyLocals⟩
    rw [hBodyEval] at bodyRel
    rcases hTargetBodyEval : evaluate (compileHOLExact bodyCtxt bodyLive body)
        { targetBody with clock := targetBody.clock + bodyClock } with
      ⟨targetResult, targetFinal⟩
    rw [hTargetBodyEval] at bodyRel bodyWorkDeriv
    obtain ⟨hFinalStateBody, hFinalMemBody, hFinalGlobalsBody, hFinalCodeBody,
      hResultBody, hLocalsBody⟩ := bodyRel
    try dsimp only at hFinalStateBody hFinalMemBody hFinalGlobalsBody hFinalCodeBody hResultBody hLocalsBody
    have hCompile : compileHOLExact ctxt l (.dec name e body) =
        .seq (loopNestedSeqHOL codePrefix)
          (.seq (.assign temporary compiledValue)
            (compileHOLExact bodyCtxt bodyLive body)) := by
      rw [compileHOLExact, hC]
    have hPrefixLift : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL codePrefix)
        { t with clock := t.clock + (prefixClock + bodyClock) } =
          (none, { prefixState with clock := prefixState.clock + bodyClock }) := by
      have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
        (loopNestedSeqHOL codePrefix) { t with clock := t.clock + prefixClock }
        none prefixState bodyClock hPrefix (by simp)
      simpa [Nat.add_assoc] using hLift
    have hAssignEval : LoopSemStateFiniteExact.evaluate (.assign temporary compiledValue)
        { prefixState with clock := prefixState.clock + bodyClock } =
          (none, { targetBody with clock := targetBody.clock + bodyClock }) := by
      rw [LoopSemStateFiniteExact.evaluate.eq_3]
      simp [LoopSemStateFiniteExact.eval_upd_clock_eq, hValue, targetBody,
        LoopSemStateFiniteExact.setVar]
    have hRun : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
        { t with clock := t.clock + (prefixClock + bodyClock) } = (targetResult, targetFinal) := by
      rw [hCompile]
      simp only [LoopSemStateFiniteExact.evaluate_seq, hPrefixLift]
      rw [hAssignEval]
      exact hTargetBodyEval
    have hResultFinal : targetResult = resultToLoop res := by
      calc
        targetResult = resultToLoop bodyResult := hResultBody
        _ = resultToLoop res := by rw [← hResult]
    have hSourceFinalLocals : s1.locals =
        bodyState.locals.resVarEq (name, v1.locals.lookup name) := by
      have hLocalsEq := congrArg (fun state : CrepSemHOLState 64 F => state.locals) hFinal
      simpa [sourceBody] using hLocalsEq.symm
    have hMakePreserve : UnassignedGoodRes targetResult → ∀ n old,
        ctxt.vars.lookup name = some n → v1.locals.lookup name = some old →
          sptLookup n targetFinal.locals = sptLookup n prefixState.locals := by
      intro hGood n old hname hOld
      have hmax := hLocalsBefore.2.1 name n hname
      have hneTmp : n ≠ temporary := by omega
      obtain ⟨mapped, hmap, hmem, hslot⟩ :=
        hLocalsBefore.2.2.2 name old hOld
      have hmapped : mapped = n := Option.some.inj (hmap.symm.trans hname)
      subst mapped
      have hslotTarget : sptLookup n targetBody.locals = some (wlabWlocHOL old) := by
        simpa [targetBody, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert,
          hneTmp, wlabWlocExact, wlabWlocHOL] using hslot
      have hNotAssigned : n ∉ holLoopAssignedVars
          (compileHOLExact bodyCtxt bodyLive body) := by
        apply not_mem_context_assigned_mem_gt bodyCtxt bodyLive body n
        refine ⟨hBodyLocals.2.1, ?_, ?_⟩
        · intro var mapped hlookup
          by_cases hvar : var = name
          · subst var
            have hmapped : temporary = mapped := by
              simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlookup
            omega
          · have hlookupOld : ctxt.vars.lookup var = some mapped := by
              simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hvar] using hlookup
            intro heq
            have hsame := hLocalsBefore.1 name var n mapped hname hlookupOld heq
            exact hvar hsame.symm
        · have hnle : n ≤ ctxt.vmax := hmax
          have hnleBody : n ≤ bodyCtxt.vmax := by
            simpa [bodyCtxt] using (Nat.le_trans hnle (Nat.le_of_lt hFresh))
          exact hnleBody
      have hLive : (sptLookup n bodyLive).isSome = true := by
        exact (sptMem_sptInsert n temporary () l).mpr (Or.inr hmem)
      have hSurvives : survivesHOLExact n
          (compileHOLExact bodyCtxt bodyLive body) = true :=
        member_cutset_survives_comp_prog bodyCtxt bodyLive body n hLive
      have hRunPreserved := unassigned_vars_evaluate_same
        (compileHOLExact bodyCtxt bodyLive body)
        { targetBody with clock := targetBody.clock + bodyClock }
        targetResult targetFinal n (wlabWlocHOL old)
        ⟨hTargetBodyEval, hGood, by
          simpa [targetBody, LoopSemStateFiniteExact.setVar] using hslotTarget,
          hNotAssigned, hSurvives⟩
      have hslotInitial : sptLookup n prefixState.locals = some (wlabWlocHOL old) := hslot
      calc
        sptLookup n targetFinal.locals = sptLookup n targetBody.locals := hRunPreserved
        _ = sptLookup n prefixState.locals := hslotTarget.trans hslotInitial.symm
    have hFinalLocals : localsResultRel ctxt l res s1 targetFinal := by
      cases res with
      | none =>
          have hGood : UnassignedGoodRes targetResult := by
            simp [hResultFinal, resultToLoop, UnassignedGoodRes]
          have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
              bodyState.locals targetFinal.locals := by
              simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
          exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
            v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
            hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
            (hMakePreserve hGood)
      | some result =>
          cases result with
          | «break» n =>
              have hGood : UnassignedGoodRes targetResult := by
                simp [hResultFinal, resultToLoop, UnassignedGoodRes]
              have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                  bodyState.locals targetFinal.locals := by
                simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
              exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                (hMakePreserve hGood)
          | «continue» n =>
              have hGood : UnassignedGoodRes targetResult := by
                simp [hResultFinal, resultToLoop, UnassignedGoodRes]
              have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                  bodyState.locals targetFinal.locals := by
                simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
              exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                (hMakePreserve hGood)
          | «return» _ => trivial
          | exception _ => trivial
          | timeOut => trivial
          | finalFfi _ => trivial
          | error =>
              exfalso
              apply hne
              rw [← hResult]
    have finalRel : LoopRunRel ctxt l (res, s1) (targetResult, targetFinal) := by
      refine ⟨?_, ?_, ?_, ?_, hResultFinal, hFinalLocals⟩
      · rw [← hFinal]
        simpa [crepToLoopStateRelExact] using hFinalStateBody
      · rw [← hFinal]
        simpa using hFinalMemBody
      · rw [← hFinal]
        simpa using hFinalGlobalsBody
      · rw [← hFinal]
        simpa [crepToLoopCodeRelExact, bodyCtxt] using hFinalCodeBody

    obtain ⟨codeCost, codeSupported, codeBound⟩ :=
      P.exprOk ctxt (ctxt.vmax + 1) l e
    rw [hC] at codeSupported codeBound
    try dsimp only at codeSupported codeBound
    obtain ⟨wp, workP, boundP⟩ := loopBounded_nestedSeq_codes codePrefix codeCost codeSupported F
      { t with clock := t.clock + (prefixClock + bodyClock) }
    rw [hPrefixLift] at workP
    have workA := LoopWork.atom (cost := loopNativeValue compiledValue) rfl hAssignEval
    have whole := LoopWork.seqNext workP (LoopWork.seqNext workA bodyWorkDeriv)
    rw [← hCompile] at whole
    refine ⟨prefixClock + bodyClock, wp + (loopNativeValue compiledValue + bodyWl), ?_, ?_, ?_⟩
    · rw [hRun]; exact whole
    · omega
    · rw [hRun, hEvalAll]; exact finalRel

#print axioms dec_loop_paid
end InitECandidate.Runtime.FineCost
