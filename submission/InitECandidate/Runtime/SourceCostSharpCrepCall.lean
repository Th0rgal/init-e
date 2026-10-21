import InitECandidate.Runtime.SourceCostSharpCrepDec
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem size_nil_context_sharp : ∀ shape : ShapeHOL,
    sizeOfShapeWithContextHOL [] shape = sizeOfShapeHOL shape := by
  refine ShapeHOL.rec
    (motive_1 := fun shape => sizeOfShapeWithContextHOL [] shape = sizeOfShapeHOL shape)
    (motive_2 := fun shapes => sizeOfShapesWithContextHOL [] shapes = sizeOfShapesHOL shapes)
    ?_ ?_ ?_ ?_ ?_
  · simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL]
  · intro shapes ih; simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL, ih]
  · intro name; simp [sizeOfShapeWithContextHOL, sizeOfShapeHOL, structContextLookupHOL_nil]
  · simp [sizeOfShapesWithContextHOL, sizeOfShapesHOL]
  · intro head tail ihHead ihTail
    simp [sizeOfShapesWithContextHOL, sizeOfShapesHOL, ihHead, ihTail]

/-- Under the simulation relation the source struct context is empty, so the
return-slot frame event is exactly the compiled slot count. -/
theorem frame_size_eq_sharp {F : Type} {context : PanToCrepContextExact 64}
    {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    (rel : SourceCrepRel context s t) (shape : ShapeHOL) :
    sizeOfShapeWithContextHOL s.structs shape = sizeOfShapeHOL shape := by
  rw [rel.state.2.2.2.1]
  exact size_nil_context_sharp shape

/-- The transfer conclusion: an executed Crep work derivation for the compiled
program from the related target state, paid by the source trace. -/
def CrepWorkPaid_sharp {F : Type} (t : CrepSemHOLState 64 F) (program : CrepProgHOL 64)
    (events : List WorkEvent) : Prop :=
  ∃ w, CrepWorkS t program w ∧ w ≤ sharpScore events

theorem expressionList_cons_events_sharp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (head : ExpHOL 64) (tail : List (ExpHOL 64)) :
    expressionListEvents s (head :: tail) = expressionEvents s head ++ expressionListEvents s tail := by
  rw [expressionListEvents]

theorem everyExpHOL_root {P : ExpHOL 64 → Bool} {e : ExpHOL 64}
    (every : everyExpHOL P e = true) : P e = true := by
  cases e <;> simp_all [everyExpHOL]

/-- Every successfully evaluated call argument pays for its compiled words. -/
theorem arguments_paid_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    (rel : SourceCrepRel context s t) :
    ∀ (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values →
      everyExpListHOL localisedExpHOL arguments = true →
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) ≤
        sharpScore ((expressionListEvents s arguments))
  | [], _, _, _ => by simp [compileExpExactHOLWList, loopPriceList]
  | head :: tail, values, evaluated, checked => by
    simp only [evalListHOLFinite, evalListHOLExact] at evaluated
    cases headValue : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) head with
    | none => rw [headValue] at evaluated; simp at evaluated
    | some value =>
      cases tailValue : @evalListHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) tail with
      | none => rw [headValue, tailValue] at evaluated; simp at evaluated
      | some rest =>
        simp only [everyExpListHOL, Bool.and_eq_true] at checked
        have headBound := compiled_expression_sharp_score s context t.locals rel.locals
          head value headValue (everyExpHOL_root checked.1)
        have tailBound := arguments_paid_sharp rel tail rest tailValue checked.2
        rw [compileExpExactHOLWList, List.flatMap_cons, loopPriceList_append,
          expressionList_cons_events_sharp, sharpScore_append]
        omega

theorem mapM_some_length_sharp {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases fa : f a with
    | none => simp [fa] at h
    | some b =>
      cases fl : l.mapM f with
      | none => simp [fa, fl] at h
      | some rs =>
        simp [fa, fl] at h
        subst h
        simp [mapM_some_length_sharp f l rs fl]

theorem crepListWork_zero_consts_sharp (n : Nat) :
    loopPriceList (List.replicate n (CrepExpHOL.const (0 : BitVec 64))) = 19 * n := by
  induction n with
  | zero => simp [loopPriceList]
  | succ n ih =>
    simp only [List.replicate_succ, loopPriceList_cons', loopNodePrice]
    rw [ih]; omega

/-- The caller state after zero-initializing compiled return slots. -/
def zeroSlotState_sharp {σ : Type} (t : CrepSemHOLState 64 σ) (rts : List Nat) :
    CrepSemHOLState 64 σ :=
  let entries := rts.zip (List.replicate rts.length (HolWordLab.word (0 : BitVec 64)))
  { t with locals := t.locals.updateListEq entries }

/-- A compiled Crep call wrapped in zero-initialized return slots. -/
theorem work_zero_slots_sharp {σ : Type} (t : CrepSemHOLState 64 σ) (rts : List Nat)
    (program : CrepProgHOL 64) (w : Nat) (nodup : rts.Nodup)
    (inner : CrepWorkS (zeroSlotState_sharp t rts) program w) :
    CrepWorkS t (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec 64))) program)
      (19 * rts.length + w) := by
  have work := work_nestedDecs_eval_sharp (List.replicate rts.length (.const (0 : BitVec 64))) rts
    (List.replicate rts.length (HolWordLab.word (0 : BitVec 64))) program t w
    (by simp [evalCrepSemHOLExp]) (by simp)
    (by simp [distinctListsHol, crepExpVarsHOL]) nodup inner
  rw [crepListWork_zero_consts_sharp] at work
  refine (congrArg (CrepWorkS t _) ?_).mp work
  omega

theorem crep_payload_le_sharp {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 r r1) :
    49 * crepCallPayloadWords r1 ≤ callExitOverhead r := by
  rcases r with _ | r
  · obtain ⟨rfl, _⟩ := rel; simp [crepCallPayloadWords]
  · cases r with
    | error => exact rel.elim
    | timeOut => simp only [pcCompileCorrectResultRel] at rel; subst rel; simp [crepCallPayloadWords]
    | «break» => obtain ⟨rfl, _⟩ := rel; simp [crepCallPayloadWords]
    | «continue» => obtain ⟨rfl, _⟩ := rel; simp [crepCallPayloadWords]
    | returned v =>
      simp only [pcCompileCorrectResultRel] at rel; subst rel
      simp [crepCallPayloadWords, callExitOverhead, callPayloadWords, returnCopy]
    | finalFfi f =>
      simp only [pcCompileCorrectResultRel] at rel; subst rel; simp [crepCallPayloadWords]
    | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel.elim
      · obtain ⟨rfl, _⟩ := rel; simp [crepCallPayloadWords, callExitOverhead, returnCopy]

theorem call_body_ok_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {info returnShape}
    {bodyResult : Option (PanSemResultExact 64)} {bodyPost : PanSemStateFiniteExact 64 F}
    {result post} (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (resultOk : result ≠ some .error) : bodyResult ≠ some .error := by
  rintro rfl
  simp only [callCostPlan, CallCostPlan.done.injEq] at plan
  exact resultOk plan.1.symm

theorem call_body_time_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {info returnShape}
    {bodyResult : Option (PanSemResultExact 64)} {bodyPost : PanSemStateFiniteExact 64 F}
    {result post} (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (resultTime : result ≠ some .timeOut) : bodyResult ≠ some .timeOut := by
  rintro rfl
  simp only [callCostPlan, CallCostPlan.done.injEq] at plan
  exact resultTime plan.1.symm

theorem everyArgs_localised_sharp {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)}
    (localised : localisedProgHOL (.call info function arguments) = true) :
    everyExpListHOL localisedExpHOL arguments = true := by
  rcases info with _ | ⟨dest, hdl⟩
  · simpa [localisedProgHOL] using localised
  · rcases dest with _ | ⟨k, n⟩ <;> rcases hdl with _ | ⟨a, b, c⟩ <;> (try rcases k) <;>
      simp_all [localisedProgHOL]

/-- A returned/propagated call exit cannot fire the compiled handler: the
source plan did not enter a handler, so a matching code would contradict the
exception-code injectivity in the original exception relation. -/
theorem done_plan_no_fire_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {context calleeContext : PanToCrepContextExact 64}
    {dest : Option (VarKind × MlStringHOL)} {hdl : Option (MlStringHOL × MlStringHOL × ProgHOL 64)}
    {returnShape : ShapeHOL} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r1 : Option (CrepResultHOLExact 64)} {result post}
    (plan : callCostPlan s (some (dest, hdl)) returnShape bodyResult bodyPost = .done result post)
    (resultOk : result ≠ some .error)
    (exceptions : panToCrepExcpRelFiniteExact context.eids s.eshapes)
    (eids : calleeContext.eids = context.eids)
    (rel : pcCompileCorrectResultRel calleeContext bodyPost t1 bodyResult r1) :
    ∀ code handler, compileCallHdlC context hdl = some (code, handler) →
      r1 ≠ some (.exception code) := by
  intro code handler fires raised
  subst raised
  rcases bodyResult with _ | r
  · obtain ⟨h, _⟩ := rel; simp at h
  cases r with
  | error => exact rel.elim
  | timeOut => simp [pcCompileCorrectResultRel] at rel
  | «break» => obtain ⟨h, _⟩ := rel; simp at h
  | «continue» => obtain ⟨h, _⟩ := rel; simp at h
  | returned v => simp [pcCompileCorrectResultRel] at rel
  | finalFfi f => simp [pcCompileCorrectResultRel] at rel
  | exception eid v =>
    simp only [pcCompileCorrectResultRel, eids] at rel
    cases hn : context.eids.lookup eid with
    | none => rw [hn] at rel; exact rel.elim
    | some n =>
    rw [hn] at rel
    obtain ⟨hcode, _⟩ := rel
    simp only [Option.some.injEq, CrepResultHOLExact.exception.injEq] at hcode
    have hn2 : context.eids.lookup eid = some code := by rw [hn]; simp only [hcode]
    rcases hdl with _ | ⟨hid, hv, hp⟩
    · simp [compileCallHdlC] at fires
    · simp only [compileCallHdlC, Option.map_eq_some_iff] at fires
      obtain ⟨code', hcode', hpair⟩ := fires
      simp only [Prod.mk.injEq] at hpair
      have same : eid = hid := exceptions.2 eid hid code code' hn2 hcode' hpair.1.symm
      subst same
      simp only [callCostPlan, ↓reduceIte] at plan
      split at plan
      · split at plan
        · simp at plan
        · simp only [CallCostPlan.done.injEq] at plan; exact resultOk plan.1.symm
      · simp only [CallCostPlan.done.injEq] at plan; exact resultOk plan.1.symm

theorem call_events_score_sharp (arguments bodyEvents : List WorkEvent) (a f x : Nat) :
    sharpScore ((.statement :: (arguments ++ [.cost (callOverhead a + slotOverhead f)] ++
      bodyEvents ++ [.cost x]))) =
    sharpScore arguments + (240 + 40 * a + 19 * f) + sharpScore bodyEvents + x := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, sharpScore_append,
    sharpScore_statement, sharpScore_cost, sharpScore_nil, callOverhead, slotOverhead]
  omega

/-- Call exits that do not enter a handler: tail calls and return-info calls
whose callee returns, times out, stops in FFI or propagates an exception. The
callee body is charged by its own trace; zero-initialized return slots are
bounded by the static signature premise. -/
theorem call_done_transfer_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)}
    {returnShape : ShapeHOL} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost : PanSemStateFiniteExact 64 F} {bodyEvents : List WorkEvent}
    {result : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.call info function arguments) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      CrepWorkPaid_sharp t' (compileProgExactHOLW context' body) bodyEvents) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.call info function arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)])) := by
  classical
  have bodyOk := call_body_ok_sharp plan resultOk
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode', hexcp',
    hloc'⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals (everyArgs_localised_sharp localised)
  obtain ⟨wb, workBody, boundBody⟩ := ihBody _ _ ⟨hst', hcode', hexcp', hloc'⟩ hprogLoc
  obtain ⟨r1, t1, hrun1, _, _, _, hrr⟩ :=
    compiled_source_run _ _ bodyRun.sound bodyOk hst' hcode' hexcp' hloc' hprogLoc
  have htclock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  have argsPaid := arguments_paid_sharp rel arguments values args (everyArgs_localised_sharp localised)
  have payload := crep_payload_le_sharp hrr
  have rsize := frame_size_eq_sharp rel returnShape
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have argPrice : sharpCrepList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) =
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
        39 * ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length := rfl
  unfold CrepWorkPaid_sharp
  rw [call_events_score_sharp, rsize]
  generalize sharpScore ((expressionListEvents s arguments)) = A
    at argsPaid ⊢
  generalize sharpScore bodyEvents = B at boundBody ⊢
  rcases info with _ | ⟨dest, hdl⟩
  · simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
    refine ⟨_, CrepWorkP.callBody htargs htlookup (by simp [crepReturnInfoNodupError]) htclock
      workBody hrun1 (by intro code rts h _ heq; simp at heq), ?_⟩
    omega
  · have noFire := done_plan_no_fire_sharp plan resultOk rel.exceptions
      (calleeContext := ctxtFcExactHOL context.funcs context.eids
        (vshapes.map Prod.fst) (vshapes.map Prod.snd)
        (List.range (sizeOfShapeHOL (.comb (vshapes.map Prod.snd)))))
      (by simp [ctxtFcExactHOL]) hrr
    have unhandled : ∀ (rts : List Nat) (code : BitVec 64) (rts' : List Nat)
        (h : CrepProgHOL 64), r1 = some (.exception code) →
        some (rts, compileCallHdlC context hdl) ≠ some (rts', some (code, h)) := by
      intro rts code rts' h hr1 heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      exact noFire code h heq.2 hr1
    rcases compileCallSomeShapeHdl context dest hdl function arguments vshapes returnShape
        rel.locals.1 hfuncs with hc | ⟨hc, _⟩ | ⟨rts0, hnd0, hc⟩
    · rw [hc]
      have hnodup : ((List.range (sizeOfShapeHOL returnShape)).map
          (fun i => context.vmax + i + 1)).Nodup :=
        List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
      have hdist := pcCompileCorrectCallRetSlotsDistinct context arguments
        (sizeOfShapeHOL returnShape) rel.locals.2.1
      have zeroArgs := optMmapEvalDistinctListsNotAffectHOL
        ((compileExpExactHOLWList context arguments).flatMap Prod.fst) t
        (values.flatMap flattenHOL)
        ((List.range (sizeOfShapeHOL returnShape)).map (fun i => context.vmax + i + 1))
        (List.replicate ((List.range (sizeOfShapeHOL returnShape)).map
          (fun i => context.vmax + i + 1)).length (HolWordLab.word (0 : BitVec 64)))
        ⟨htargs, by simp, hdist⟩
      have inner := CrepWorkP.callBody (t := zeroSlotState_sharp t _) (returnInfo := some (_,
        compileCallHdlC context hdl)) zeroArgs htlookup
        (by simpa [crepReturnInfoNodupError] using hnodup) htclock workBody hrun1
        (by intro code rts h hr1; exact unhandled _ code rts h hr1)
      refine ⟨_, work_zero_slots_sharp t _ _ _ hnodup inner, ?_⟩
      simp only [List.length_map, List.length_range] at payload ⊢
      omega
    · rw [hc]
      refine ⟨_, CrepWorkP.callBody htargs htlookup (by simp [crepReturnInfoNodupError]) htclock
        workBody hrun1 (by intro code rts h _ heq; simp at heq), ?_⟩
      omega
    · rw [hc]
      refine ⟨_, CrepWorkP.callBody htargs htlookup (by simpa [crepReturnInfoNodupError] using hnd0)
        htclock workBody hrun1 (by intro code rts h hr1; exact unhandled _ code rts h hr1), ?_⟩
      omega

theorem handler_plan_info_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {returnShape : ShapeHOL} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost entry : PanSemStateFiniteExact 64 F} {program : ProgHOL 64}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    ∃ dest exceptionId handlerVar, info = some (dest, some (exceptionId, handlerVar, program)) := by
  rcases bodyResult with _ | r
  · simp [callCostPlan] at plan
  cases r with
  | returned v =>
    simp only [callCostPlan] at plan
    split at plan
    · split at plan
      · simp at plan
      · simp at plan
      · split at plan <;> simp at plan
    · simp at plan
  | exception eid v =>
    simp only [callCostPlan] at plan
    split at plan
    · simp at plan
    · simp at plan
    · rename_i dest hid hv hp
      split at plan
      · split at plan
        · split at plan
          · simp only [CallCostPlan.handler.injEq] at plan
            exact ⟨dest, hid, hv, by rw [plan.2]⟩
          · simp at plan
        · simp at plan
      · simp at plan
  | _ => simp [callCostPlan] at plan

/-- A call reaching a zero clock after argument evaluation and lookup times out
before entering the callee; only the arguments and any return-slot setup ran. -/
theorem call_timeout_transfer_sharp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)}
    {returnShape : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.call info function arguments) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true)
    :
    CrepWorkPaid_sharp t (compileProgExactHOLW context (.call info function arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape))])) := by
  classical
  obtain ⟨vshapes, _hsrc, _, hfuncs, _hlen, htargs, htlookup, _, _, _, _⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals (everyArgs_localised_sharp localised)
  have htclock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  have argsPaid := arguments_paid_sharp rel arguments values args (everyArgs_localised_sharp localised)
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have argPrice : sharpCrepList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) =
      loopPriceList ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
        39 * ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length := rfl
  have rsize := frame_size_eq_sharp rel returnShape
  unfold CrepWorkPaid_sharp
  simp only [sharpScore_statement, sharpScore_append, sharpScore_cost, sharpScore_nil, rsize,
    callOverhead, slotOverhead]
  generalize sharpScore (expressionListEvents s arguments) = A at argsPaid ⊢
  have short : ∀ (t'' : CrepSemHOLState 64 F) ri,
      ((compileExpExactHOLWList context arguments).flatMap Prod.fst).mapM
        (evalCrepSemHOLExp t'') = some (values.flatMap flattenHOL) → t''.code = t.code →
      t''.clock = t.clock →
      CrepWorkS t'' (.call ri function ((compileExpExactHOLWList context arguments).flatMap
        Prod.fst)) (240 + sharpCrepList ((compileExpExactHOLWList context arguments).flatMap
          Prod.fst)) := by
    intro t'' ri hargs hcode hclk
    exact CrepWorkP.callShort (Or.inr ⟨_, hargs, Or.inr (Or.inr (by rw [hclk]; exact htclock))⟩)
  rcases info with _ | ⟨dest, hdl⟩
  · simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
    exact ⟨_, short t none htargs rfl rfl, by omega⟩
  · rcases compileCallSomeShapeHdl context dest hdl function arguments vshapes returnShape
        rel.locals.1 hfuncs with hc | ⟨hc, _⟩ | ⟨rts0, _, hc⟩
    · rw [hc]
      have hnodup : ((List.range (sizeOfShapeHOL returnShape)).map
          (fun i => context.vmax + i + 1)).Nodup :=
        List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
      have hdist := pcCompileCorrectCallRetSlotsDistinct context arguments
        (sizeOfShapeHOL returnShape) rel.locals.2.1
      have zeroArgs := optMmapEvalDistinctListsNotAffectHOL
        ((compileExpExactHOLWList context arguments).flatMap Prod.fst) t
        (values.flatMap flattenHOL)
        ((List.range (sizeOfShapeHOL returnShape)).map (fun i => context.vmax + i + 1))
        (List.replicate ((List.range (sizeOfShapeHOL returnShape)).map
          (fun i => context.vmax + i + 1)).length (HolWordLab.word (0 : BitVec 64)))
        ⟨htargs, by simp, hdist⟩
      refine ⟨_, work_zero_slots_sharp t _ _ _ hnodup
        (short (zeroSlotState_sharp t _) _ zeroArgs rfl rfl), ?_⟩
      simp only [List.length_map, List.length_range]
      omega
    · rw [hc]; exact ⟨_, short t _ htargs rfl rfl, by omega⟩
    · rw [hc]; exact ⟨_, short t _ htargs rfl rfl, by omega⟩

#print axioms handler_plan_info_sharp
#print axioms call_timeout_transfer_sharp
#print axioms call_body_time_sharp
#print axioms call_done_transfer_sharp
#print axioms arguments_paid_sharp
#print axioms work_zero_slots_sharp
#print axioms crep_payload_le_sharp
#print axioms done_plan_no_fire_sharp
end InitECandidate.Runtime.FineCost
