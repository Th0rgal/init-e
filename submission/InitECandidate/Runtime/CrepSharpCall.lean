import InitECandidate.Runtime.CrepSharpDec
import InitECandidate.Runtime.SourceCostSharpCrepCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace SharpModel
variable (M : SharpModel) {fn : Flapjack.Pancake.PanLang.MlS}

/-- The one-off charge of a stopped call, due only on a timed-out trace. -/
def stopP : Option (PanSemResultExact 64) → Nat
  | some .timeOut => M.shortP
  | _ => 0

theorem stopP_le (r : Option (PanSemResultExact 64)) : M.stopP r ≤ M.shortP := by
  unfold stopP; split <;> omega

theorem stopP_done {F : Type} {s : PanSemStateFiniteExact 64 F} {info returnShape}
    {bodyResult : Option (PanSemResultExact 64)} {bodyPost : PanSemStateFiniteExact 64 F}
    {result post} (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    M.stopP bodyResult ≤ M.stopP result := by
  by_cases h : result = some .timeOut
  · subst h; exact M.stopP_le _
  · have := call_body_time_sharp plan h
    have : M.stopP bodyResult = 0 := by
      unfold stopP; split
      · exact absurd rfl this
      · rfl
    omega

theorem call_events_score (arguments bodyEvents : List WorkEvent) (a f x m : Nat) :
    sharpScore ((.statement :: (arguments ++ [.cost (callOverhead a + slotOverhead f + m)] ++
      bodyEvents ++ [.cost x]))) =
    sharpScore arguments + (callOverhead a + slotOverhead f + m) + sharpScore bodyEvents + x := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, sharpScore_append,
    sharpScore_statement, sharpScore_cost, sharpScore_nil]
  omega

/-- The transfer conclusion: an executed model-priced Crep work derivation for
the compiled program from the related target state, paid by the source trace
plus `extra` (a stopped call's one-off charge). -/
def CrepWorkPaidM {F : Type} (t : CrepSemHOLState 64 F) (program : CrepProgHOL 64)
    (events : List WorkEvent) (extra : Nat) : Prop :=
  ∃ w, CrepWorkM M fn t program w ∧ w ≤ sharpScore events + extra

/-- Every successfully evaluated call argument pays for its compiled words. -/
theorem arguments_paid {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    (rel : SourceCrepRel context s t) :
    ∀ (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values →
      everyExpListHOL localisedExpHOL arguments = true →
      nodePriceListK M.K ((compileExpExactHOLWList context arguments).flatMap Prod.fst) ≤
        sharpScore ((expressionListEvents s arguments))
  | [], _, _, _ => by simp [compileExpExactHOLWList, nodePriceListK]
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
        have headBound := M.expression_paid s context t.locals rel.locals
          head value headValue (everyExpHOL_root checked.1)
        have tailBound := arguments_paid rel tail rest tailValue checked.2
        rw [compileExpExactHOLWList, List.flatMap_cons, nodePriceListK_append,
          expressionList_cons_events_sharp, sharpScore_append]
        omega

theorem zero_consts_price (n : Nat) :
    nodePriceListK M.K (List.replicate n (CrepExpHOL.const (0 : BitVec 64))) = n * M.K.cst := by
  induction n with
  | zero => simp [nodePriceListK]
  | succ n ih =>
    simp only [List.replicate_succ, nodePriceListK_cons, nodePriceK]
    rw [ih, Nat.succ_mul]; omega

/-- A compiled Crep call wrapped in zero-initialized return slots. -/
theorem work_zero_slots {σ : Type} (t : CrepSemHOLState 64 σ) (rts : List Nat)
    (program : CrepProgHOL 64) (w : Nat) (nodup : rts.Nodup)
    (inner : CrepWorkM M fn (zeroSlotState_sharp t rts) program w) :
    CrepWorkM M fn t (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec 64))) program)
      (rts.length * M.K.cst + w) := by
  have work := M.work_nestedDecs_eval (List.replicate rts.length (.const (0 : BitVec 64))) rts
    (List.replicate rts.length (HolWordLab.word (0 : BitVec 64))) program t w
    (by simp [evalCrepSemHOLExp]) (by simp)
    (by simp [distinctListsHol, crepExpVarsHOL]) nodup inner
  rw [zero_consts_price] at work
  exact work

theorem exit_le {F : Type} {context : PanToCrepContextExact 64}
    {post : PanSemStateFiniteExact 64 F} {t1 : CrepSemHOLState 64 F}
    {r : Option (PanSemResultExact 64)} {r1 : Option (CrepResultHOLExact 64)}
    (rel : pcCompileCorrectResultRel context post t1 r r1) :
    M.S.exit r1 ≤ callExitOverhead r := by
  rcases r with _ | r
  · obtain ⟨rfl, _⟩ := rel; simp [StmtK.exit]
  · cases r with
    | error => exact rel.elim
    | timeOut => simp only [pcCompileCorrectResultRel] at rel; subst rel; simp [StmtK.exit]
    | «break» => obtain ⟨rfl, _⟩ := rel; simp [StmtK.exit]
    | «continue» => obtain ⟨rfl, _⟩ := rel; simp [StmtK.exit]
    | returned v =>
      simp only [pcCompileCorrectResultRel] at rel; subst rel
      simp only [StmtK.exit, callExitOverhead, callPayloadWords, List.length_map]
      exact M.retWOk _
    | finalFfi f =>
      simp only [pcCompileCorrectResultRel] at rel; subst rel; simp [StmtK.exit]
    | exception eid v =>
      simp only [pcCompileCorrectResultRel] at rel
      split at rel
      · exact rel.elim
      · obtain ⟨rfl, _⟩ := rel; simp only [StmtK.exit, callExitOverhead]; exact M.exnOk _

/-- Call exits that do not enter a handler: tail calls and return-info calls
whose callee returns, times out, stops in FFI or propagates an exception. The
callee body is charged by its own trace; zero-initialized return slots are
bounded by the static signature premise. -/
theorem call_done_transfer {F : Type} {s : PanSemStateFiniteExact 64 F}
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
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (resultOk : result ≠ some .error)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.call info function arguments) = true)
    (checkedArgs : sharpSitesList sharpReplayBound arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      M.CrepWorkPaidM (fn := function) t' (compileProgExactHOLW context' body) bodyEvents
        (M.stopP bodyResult)) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context (.call info function arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape) +
            (callMoves fn function + callSites fn function))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)])) (M.stopP result) := by
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
  have argsPaid := M.arguments_paid rel arguments values args (everyArgs_localised_sharp localised)
  have payload := M.exit_le hrr
  have rsize := frame_size_eq_sharp rel returnShape
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have stop := M.stopP_done plan
  have slots := M.slotOk (sizeOfShapeHOL returnShape)
  have callFit := M.callOk fn function
  have argFit : ∀ n, M.callP fn function n +
      M.S.argP ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length ≤
      callOverhead (values.flatMap flattenHOL).length + callSites fn function := by
    intro n; rw [← argLen]; exact callFit n _
  unfold CrepWorkPaidM
  rw [call_events_score, rsize]
  generalize sharpScore ((expressionListEvents s arguments)) = A
    at argsPaid ⊢
  generalize sharpScore bodyEvents = B at boundBody ⊢
  generalize callOverhead (values.flatMap flattenHOL).length = C at argFit ⊢
  generalize slotOverhead (sizeOfShapeHOL returnShape) = D at slots ⊢
  rcases info with _ | ⟨dest, hdl⟩
  · simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
    refine ⟨_, CrepWorkF.callBody htargs htlookup (by simp [crepReturnInfoNodupError]) htclock
      workBody hrun1 (by intro code rts h _ heq; simp at heq), ?_⟩
    have := argFit 0; simp only [crepRetCount]; omega
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
      have inner := CrepWorkF.callBody (fn := fn) (t := zeroSlotState_sharp t _) (returnInfo := some (_,
        compileCallHdlC context hdl)) zeroArgs htlookup
        (by simpa [crepReturnInfoNodupError] using hnodup) htclock workBody hrun1
        (by intro code rts h hr1; exact unhandled _ code rts h hr1)
      refine ⟨_, M.work_zero_slots t _ _ _ hnodup inner, ?_⟩
      have := argFit (sizeOfShapeHOL returnShape)
      simp only [crepRetCount, List.length_map, List.length_range] at payload ⊢
      omega
    · rw [hc]
      refine ⟨_, CrepWorkF.callBody htargs htlookup (by simp [crepReturnInfoNodupError]) htclock
        workBody hrun1 (by intro code rts h _ heq; simp at heq), ?_⟩
      have := argFit 0; simp only [crepRetCount]; omega
    · rw [hc]
      refine ⟨_, CrepWorkF.callBody htargs htlookup (by simpa [crepReturnInfoNodupError] using hnd0)
        htclock workBody hrun1 (by intro code rts h hr1; exact unhandled _ code rts h hr1), ?_⟩
      have := argFit rts0.length; simp only [crepRetCount]; omega

/-- A call reaching a zero clock after argument evaluation and lookup times out
before entering the callee; only the arguments and any return-slot setup ran. -/
theorem call_timeout_transfer {F : Type} {s : PanSemStateFiniteExact 64 F}
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
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context (.call info function arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape) +
            (callMoves fn function + callSites fn function))])) (M.stopP (some .timeOut)) := by
  classical
  obtain ⟨vshapes, _hsrc, _, hfuncs, _hlen, htargs, htlookup, _, _, _, _⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals (everyArgs_localised_sharp localised)
  have htclock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  have argsPaid := M.arguments_paid rel arguments values args (everyArgs_localised_sharp localised)
  have argLen := mapM_some_length_sharp _ _ _ htargs
  have rsize := frame_size_eq_sharp rel returnShape
  have slots := M.slotOk (sizeOfShapeHOL returnShape)
  have callFit := M.callOk fn function
  have argFit : ∀ n, M.callP fn function n +
      M.S.argP ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length ≤
      callOverhead (values.flatMap flattenHOL).length + callSites fn function := by
    intro n; rw [← argLen]; exact callFit n _
  unfold CrepWorkPaidM
  simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_cost, sharpScore_nil, rsize]
  generalize sharpScore (expressionListEvents s arguments) = A at argsPaid ⊢
  generalize callOverhead (values.flatMap flattenHOL).length = C at argFit ⊢
  generalize slotOverhead (sizeOfShapeHOL returnShape) = D at slots ⊢
  have short : ∀ (t'' : CrepSemHOLState 64 F) ri,
      ((compileExpExactHOLWList context arguments).flatMap Prod.fst).mapM
        (evalCrepSemHOLExp t'') = some (values.flatMap flattenHOL) → t''.code = t.code →
      t''.clock = t.clock →
      CrepWorkM M fn t'' (.call ri function ((compileExpExactHOLWList context arguments).flatMap
        Prod.fst)) (M.callP fn function (crepRetCount ri) + M.shortP +
          nodePriceListK M.K ((compileExpExactHOLWList context arguments).flatMap Prod.fst) +
          M.S.argP ((compileExpExactHOLWList context arguments).flatMap Prod.fst).length) := by
    intro t'' ri hargs hcode hclk
    exact CrepWorkF.callShort (Or.inr ⟨_, hargs, Or.inr (Or.inr (by rw [hclk]; exact htclock))⟩)
  rcases info with _ | ⟨dest, hdl⟩
  · simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
    exact ⟨_, short t none htargs rfl rfl, by have := argFit 0; simp only [crepRetCount]; omega⟩
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
      refine ⟨_, M.work_zero_slots t _ _ _ hnodup
        (short (zeroSlotState_sharp t _) _ zeroArgs rfl rfl), ?_⟩
      have := argFit (sizeOfShapeHOL returnShape)
      simp only [crepRetCount, List.length_map, List.length_range]
      omega
    · rw [hc]; exact ⟨_, short t _ htargs rfl rfl, by have := argFit 0; simp only [crepRetCount]; omega⟩
    · rw [hc]; exact ⟨_, short t _ htargs rfl rfl, by
        have := argFit rts0.length; simp only [crepRetCount]; omega⟩

end SharpModel

#print axioms SharpModel.call_done_transfer
#print axioms SharpModel.call_timeout_transfer
#print axioms SharpModel.arguments_paid
end InitECandidate.Runtime.FineCost
