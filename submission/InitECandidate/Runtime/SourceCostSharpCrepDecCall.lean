import InitECandidate.Runtime.SourceCostSharpCrepHandler
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem decCall_events_score_sharp (arguments bodyEvents continuationEvents : List WorkEvent)
    (a f c m : Nat) :
    sharpScore ((.statement :: (arguments ++ [.cost (callOverhead a + slotOverhead f + m)] ++
      bodyEvents ++ [.cost (returnCopy c)] ++ continuationEvents))) =
    sharpScore arguments + (196 + 40 * a + 19 * f + m) + sharpScore bodyEvents + 49 * c +
      sharpScore continuationEvents := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, sharpScore_append,
    sharpScore_statement, sharpScore_cost, sharpScore_copy, sharpScore_nil, callOverhead,
    slotOverhead, returnCopy]
  omega

/-- Common prelude of every positive-clock declared call: argument evaluation,
target lookup, the callee body work and its compiled run with all relations. -/
theorem decCall_prelude_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {function : MlStringHOL} {arguments : List (ExpHOL 64)}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)} {returnShape : ShapeHOL}
    {bodyResult : Option (PanSemResultExact 64)} {bodyPost : PanSemStateFiniteExact 64 F}
    {bodyEvents : List WorkEvent}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (bodyOk : bodyResult ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localisedArgs : everyExpListHOL localisedExpHOL arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      CrepWorkPaid_sharp t' (compileProgExactHOLW context' body) bodyEvents) :
    ∃ (calleeContext : PanToCrepContextExact 64) (crepBody : CrepProgHOL 64)
      (locals : HolFiniteMapExact Nat (HolWordLab 64)) (wb : Nat)
      (r1 : Option (CrepResultHOLExact 64)) (t1 : CrepSemHOLState 64 F),
    calleeContext.eids = context.eids ∧
    ((compileExpExactHOLWList context arguments).flatMap Prod.fst).mapM (evalCrepSemHOLExp t) =
      some (values.flatMap flattenHOL) ∧
    lookupCodeFiniteHOL t.code function (values.flatMap flattenHOL)
      (values.flatMap flattenHOL).length = some (crepBody, locals) ∧
    CrepWorkS { decClockCrepSemHOL t with locals := locals } crepBody wb ∧
    wb ≤ sharpScore bodyEvents ∧
    evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } crepBody = (r1, t1) ∧
    panToCrepStateRelFiniteExact bodyPost t1 ∧ codeRelExactHOLW context bodyPost.code t1.code ∧
    panToCrepExcpRelFiniteExact context.eids bodyPost.eshapes ∧
    pcCompileCorrectResultRel calleeContext bodyPost t1 bodyResult r1 := by
  classical
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode', hexcp',
    hloc'⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals localisedArgs
  obtain ⟨wb, workBody, boundBody⟩ := ihBody _ _ ⟨hst', hcode', hexcp', hloc'⟩ hprogLoc
  obtain ⟨r1, t1, hrun1, hs, hc, he, hrr⟩ :=
    compiled_source_run _ _ bodyRun.sound bodyOk hst' hcode' hexcp' hloc' hprogLoc
  exact ⟨ctxtFcExactHOL context.funcs context.eids (vshapes.map Prod.fst) (vshapes.map Prod.snd)
      (List.range (sizeOfShapeHOL (.comb (vshapes.map Prod.snd)))), _, _, wb, r1, t1,
    by simp [ctxtFcExactHOL], htargs, htlookup, workBody, boundBody,
    hrun1, hs, codeRelExactHOLW_ctxtFc context _ _ _ _ _ hc, he, hrr⟩

theorem decCall_call_run_sharp {σ : Type} (t : CrepSemHOLState 64 σ) (slots : List Nat)
    (function : MlStringHOL) (cargs : List (CrepExpHOL 64)) (flat : List (HolWordLab 64))
    (crepBody : CrepProgHOL 64) (locals : HolFiniteMapExact Nat (HolWordLab 64))
    (nodup : slots.Nodup)
    (hdist : distinctListsHol slots (cargs.flatMap crepExpVarsHOL) = true)
    (hargs : cargs.mapM (evalCrepSemHOLExp t) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code function flat flat.length = some (crepBody, locals))
    (clock : t.clock ≠ 0) :
    cargs.mapM (evalCrepSemHOLExp (zeroSlotState_sharp t slots)) = some flat ∧
    evalCrepSemHOLProgExact (zeroSlotState_sharp t slots) (.call (some (slots, none)) function cargs) =
      crepCallAfterBody (zeroSlotState_sharp t slots) (some (slots, none))
        (evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } crepBody) := by
  classical
  have zeroArgs := optMmapEvalDistinctListsNotAffectHOL cargs t flat slots
    (List.replicate slots.length (HolWordLab.word (0 : BitVec 64))) ⟨hargs, by simp, hdist⟩
  refine ⟨zeroArgs, ?_⟩
  have hg : ∀ rts' h, (some (slots, none) : Option (List Nat × Option (BitVec 64 × CrepProgHOL 64))) =
      some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact nodup
  exact crepCallTarget (zeroSlotState_sharp t slots) (some (slots, none)) function cargs flat crepBody
    locals zeroArgs hlookup hg clock

/-- Declared call whose callee returns a value of the declared shape: slot
setup, call, returned-word copy and the continuation in the extended context. -/
theorem decCall_return_transfer_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {name : MlStringHOL}
    {shape : ShapeHOL} {function : MlStringHOL} {arguments : List (ExpHOL 64)}
    {continuation : ProgHOL 64} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)} {returnShape : ShapeHOL}
    {value : ValueHOL 64} {bodyPost : PanSemStateFiniteExact 64 F}
    {bodyEvents continuationEvents : List WorkEvent}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body
      (some (.returned value)) bodyPost bodyEvents)
    (shapeMatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
      shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.decCall name shape function arguments continuation) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      CrepWorkPaid_sharp t' (compileProgExactHOLW context' body) bodyEvents)
    (ihContinuation : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (setVarHOLFinite name value { bodyPost with locals := s.locals }) t' →
      CrepWorkPaid_sharp t' (compileProgExactHOLW context' continuation) continuationEvents) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.decCall name shape function arguments
        continuation))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))] ++ bodyEvents ++
        [.cost (returnCopy (flattenHOL value).length)] ++ continuationEvents)) := by
  classical
  have localisedAll : everyExpListHOL localisedExpHOL arguments = true ∧
      localisedProgHOL continuation = true := by
    simpa [localisedProgHOL] using localised
  obtain ⟨calleeContext, crepBody, locals, wb, r1, t1, _, htargs, htlookup, workBody, boundBody,
    hrun1, hs, hc, he, hrr⟩ :=
    decCall_prelude_sharp args lookup bodyRun (by simp) rel localisedAll.1 ihBody
  simp only [pcCompileCorrectResultRel] at hrr
  subst hrr
  simp only [Bool.and_eq_true] at shapeMatch
  have h1 : shapeOfHOLExact value = shape := (shapeEqHOL_eq_true _ _).mp shapeMatch.1
  have hwfv : isWfShapeValueHOLExact [] value = true := by
    have := panToCrepFiniteEvaluateShapeInvariantRetInst2 arguments s function values body
      callee returnShape body (.returned value) bodyPost t context t.locals
      (by simpa [evalListHOLFiniteClassical] using args)
      (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ lookup) bodyRun.sound
      rel.state rel.locals
    simpa using this
  have hwf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
    rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl value]
    exact hwfv
  have hflen : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact value) :=
    flattenHOL_length_eq_sizeOfShapeHOL value hwf
  have hnodup := decCallSlots_nodup context shape
  have hlenS : (flattenHOL value).length = (decCallSlots context shape).length := by
    simp [decCallSlots, hflen, h1]
  have hzlen : (decCallSlots context shape).length =
      (List.replicate (decCallSlots context shape).length
        (HolWordLab.word (0 : BitVec 64))).length := by simp
  have hdist := pcCompileCorrectCallRetSlotsDistinct context arguments (sizeOfShapeHOL shape)
    rel.locals.2.1
  have htclock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  obtain ⟨zeroArgs, hcall⟩ := decCall_call_run_sharp t (decCallSlots context shape) function _ _ _ _
    hnodup hdist htargs htlookup htclock
  rw [hrun1] at hcall
  have hcallres : crepCallAfterBody (zeroSlotState_sharp t (decCallSlots context shape))
      (some (decCallSlots context shape, none)) (some (.return (flattenHOL value)), t1) =
      (none, { t1 with locals :=
        t.locals.updateListEq ((decCallSlots context shape).zip (flattenHOL value)) }) := by
    simp only [zeroSlotState_sharp]
    simp only [crepCallAfterBody]
    rw [if_neg (by rw [hlenS]; exact fun h => h rfl)]
    rw [mapM_lookup_updateListEq _ _ _ hnodup hzlen]
    dsimp only
    rw [updateListEq_overwrite t.locals _ _ _ hzlen hlenS.symm]
  rw [hcallres] at hcall
  have hlocc := localsRelExtendNewVarHOL context s.locals t.locals value name
    (decCallSlots context shape)
    ⟨rel.locals, hwf, hnodup, fun y hy => by
      have := decCallSlots_gt context shape y hy; rw [h1]; exact this,
      by rw [← hlenS, hflen]⟩
  rw [h1] at hlocc
  obtain ⟨wc, workCont, boundCont⟩ := ihContinuation
    ({ t1 with locals := t.locals.updateListEq ((decCallSlots context shape).zip
      (flattenHOL value)) } : CrepSemHOLState 64 F) (decCallCtxt context name shape)
    ⟨by simpa [panToCrepStateRelFiniteExact, setVarHOLFinite] using hs, hc, he, hlocc⟩
  have inner := CrepWorkS.seqNext (second := compileProgExactHOLW
      (decCallCtxt context name shape) continuation)
    (CrepWorkS.callBody (t := zeroSlotState_sharp t (decCallSlots context shape))
      (returnInfo := some (decCallSlots context shape, none)) zeroArgs htlookup
      (by simpa [crepReturnInfoNodupError] using hnodup) htclock workBody hrun1
      (by intro code rts h _ heq; simp at heq)) hcall workCont
  have argsPaid := arguments_paid_sharp rel arguments values args localisedAll.1
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have argPrice : sharpCrepList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) =
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
        39 * ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length := rfl
  unfold CrepWorkPaid_sharp
  rw [compileDecCallShape, decCall_events_score_sharp, frame_size_eq_sharp rel shape]
  refine ⟨_, work_zero_slots_sharp t _ _ _ hnodup inner, ?_⟩
  simp only [crepCallPayloadWords, List.length_map, List.length_range] at hlenS ⊢
  rw [← hlenS]
  omega

theorem decCall_timeout_transfer_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {name : MlStringHOL}
    {shape : ShapeHOL} {function : MlStringHOL} {arguments : List (ExpHOL 64)}
    {continuation : ProgHOL 64} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)} {returnShape : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.decCall name shape function arguments continuation) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.decCall name shape function arguments
        continuation))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))])) := by
  classical
  have localisedAll : everyExpListHOL localisedExpHOL arguments = true ∧
      localisedProgHOL continuation = true := by
    simpa [localisedProgHOL] using localised
  obtain ⟨vshapes, _hsrc, _, _, _hlen, htargs, htlookup, _, _, _, _⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals localisedAll.1
  have htclock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  have hnodup := decCallSlots_nodup context shape
  have hdist := pcCompileCorrectCallRetSlotsDistinct context arguments (sizeOfShapeHOL shape)
    rel.locals.2.1
  have zeroArgs := optMmapEvalDistinctListsNotAffectHOL
    ((compileExpExactHOLWList context arguments).flatMap Prod.fst) t
    (values.flatMap flattenHOL) (decCallSlots context shape)
    (List.replicate (decCallSlots context shape).length (HolWordLab.word (0 : BitVec 64)))
    ⟨htargs, by simp, hdist⟩
  have hg : ∀ rts' h, (some (decCallSlots context shape, none) :
      Option (List Nat × Option (BitVec 64 × CrepProgHOL 64))) = some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]
    exact hnodup
  have run := crepCallTimeout (zeroSlotState_sharp t (decCallSlots context shape))
    (some (decCallSlots context shape, none)) function _ _ _ _ zeroArgs htlookup hg htclock
  have inner := CrepWorkS.seqStop (second := compileProgExactHOLW
      (decCallCtxt context name shape) continuation)
    (CrepWorkS.callShort (t := zeroSlotState_sharp t (decCallSlots context shape))
      (returnInfo := some (decCallSlots context shape, none)) (function := function)
      (Or.inr ⟨_, zeroArgs, Or.inr (Or.inr htclock)⟩)) run
  have argsPaid := arguments_paid_sharp rel arguments values args localisedAll.1
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have argPrice : sharpCrepList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) =
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
        39 * ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length := rfl
  unfold CrepWorkPaid_sharp
  rw [compileDecCallShape, frame_size_eq_sharp rel shape]
  simp only [sharpScore_statement, sharpScore_append, sharpScore_cost, sharpScore_nil,
    callOverhead, slotOverhead]
  refine ⟨_, work_zero_slots_sharp t _ _ _ hnodup inner, ?_⟩
  simp only [List.length_map, List.length_range] at argsPaid ⊢
  omega

theorem stopped_after_body_sharp {σ : Type} {calleeContext : PanToCrepContextExact 64}
    {bodyPost : PanSemStateFiniteExact 64 σ} {t1 t' : CrepSemHOLState 64 σ}
    {bodyResult : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (slots : List Nat) (hrr : pcCompileCorrectResultRel calleeContext bodyPost t1 bodyResult r1)
    (stop : bodyResult = some .timeOut ∨ (∃ f, bodyResult = some (.finalFfi f)) ∨
      ∃ eid v, bodyResult = some (.exception eid v)) :
    ∃ r t2, crepCallAfterBody t' (some (slots, none)) (r1, t1) = (some r, t2) := by
  rcases stop with rfl | ⟨f, rfl⟩ | ⟨eid, v, rfl⟩
  · simp only [pcCompileCorrectResultRel] at hrr; subst hrr
    exact ⟨_, _, by simp only [crepCallAfterBody]; rfl⟩
  · simp only [pcCompileCorrectResultRel] at hrr; subst hrr
    exact ⟨_, _, by simp only [crepCallAfterBody]; rfl⟩
  · simp only [pcCompileCorrectResultRel] at hrr
    split at hrr
    · exact hrr.elim
    · obtain ⟨rfl, _⟩ := hrr
      exact ⟨_, _, by simp only [crepCallAfterBody]; rfl⟩

theorem decCall_stop_cases_sharp {F : Type} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost : PanSemStateFiniteExact 64 F}
    (terminal : ∀ value, bodyResult ≠ some (.returned value))
    (resultOk : (declareCallStopPlan bodyResult bodyPost).1 ≠ some .error) :
    bodyResult = some .timeOut ∨ (∃ f, bodyResult = some (.finalFfi f)) ∨
      ∃ eid v, bodyResult = some (.exception eid v) := by
  rcases bodyResult with _ | r
  · simp [declareCallStopPlan] at resultOk
  cases r with
  | returned v => exact absurd rfl (terminal v)
  | timeOut => exact Or.inl rfl
  | finalFfi f => exact Or.inr (Or.inl ⟨f, rfl⟩)
  | exception eid v => exact Or.inr (Or.inr ⟨eid, v, rfl⟩)
  | _ => simp [declareCallStopPlan] at resultOk

/-- Declared call whose callee stops (timeout, final FFI or exception): the
continuation is never entered. -/
theorem decCall_stopped_transfer_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64} {name : MlStringHOL}
    {shape : ShapeHOL} {function : MlStringHOL} {arguments : List (ExpHOL 64)}
    {continuation : ProgHOL 64} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)} {returnShape : ShapeHOL}
    {bodyResult : Option (PanSemResultExact 64)} {bodyPost : PanSemStateFiniteExact 64 F}
    {bodyEvents : List WorkEvent}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (stop : bodyResult = some .timeOut ∨ (∃ f, bodyResult = some (.finalFfi f)) ∨
      ∃ eid v, bodyResult = some (.exception eid v))
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.decCall name shape function arguments continuation) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      CrepWorkPaid_sharp t' (compileProgExactHOLW context' body) bodyEvents) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.decCall name shape function arguments
        continuation))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)])) := by
  classical
  have localisedAll : everyExpListHOL localisedExpHOL arguments = true ∧
      localisedProgHOL continuation = true := by
    simpa [localisedProgHOL] using localised
  have bodyOk : bodyResult ≠ some .error := by
    rcases stop with rfl | ⟨f, rfl⟩ | ⟨eid, v, rfl⟩ <;> simp
  obtain ⟨calleeContext, crepBody, locals, wb, r1, t1, _, htargs, htlookup, workBody, boundBody,
    hrun1, _, _, _, hrr⟩ :=
    decCall_prelude_sharp args lookup bodyRun bodyOk rel localisedAll.1 ihBody
  have payload := crep_payload_le_sharp hrr
  have hnodup := decCallSlots_nodup context shape
  have hdist := pcCompileCorrectCallRetSlotsDistinct context arguments (sizeOfShapeHOL shape)
    rel.locals.2.1
  have htclock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  obtain ⟨zeroArgs, hcall⟩ := decCall_call_run_sharp t (decCallSlots context shape) function _ _ _ _
    hnodup hdist htargs htlookup htclock
  rw [hrun1] at hcall
  obtain ⟨r, t2, hstop⟩ := stopped_after_body_sharp (t' := zeroSlotState_sharp t (decCallSlots context shape))
    (decCallSlots context shape) hrr stop
  rw [hstop] at hcall
  have inner := CrepWorkS.seqStop (second := compileProgExactHOLW
      (decCallCtxt context name shape) continuation)
    (CrepWorkS.callBody (t := zeroSlotState_sharp t (decCallSlots context shape))
      (returnInfo := some (decCallSlots context shape, none)) zeroArgs htlookup
      (by simpa [crepReturnInfoNodupError] using hnodup) htclock workBody hrun1
      (by intro code rts h _ heq; simp at heq)) hcall
  have argsPaid := arguments_paid_sharp rel arguments values args localisedAll.1
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have argPrice : sharpCrepList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) =
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
        39 * ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length := rfl
  unfold CrepWorkPaid_sharp
  rw [compileDecCallShape, call_events_score_sharp, frame_size_eq_sharp rel shape]
  refine ⟨_, work_zero_slots_sharp t _ _ _ hnodup inner, ?_⟩
  simp only [List.length_map, List.length_range]
  omega

#print axioms decCall_timeout_transfer_sharp
#print axioms decCall_stopped_transfer_sharp
#print axioms decCall_return_transfer_sharp
end InitECandidate.Runtime.FineCost
