import InitECandidate.Runtime.SourceCostCrepCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem bounded_load_globals (names : List Nat) (address : BitVec 5) :
    CrepBounded (crepNestedSeqHOL (panMap2 (fun destination source => .assign destination source)
      names (loadGlobalsHOL address names.length))) (1 + 3 * names.length) := by
  induction names generalizing address with
  | nil => simpa [panMap2, crepNestedSeqHOL] using bounded_skip
  | cons name names ih =>
    simp only [List.length_cons, loadGlobalsHOL, panMap2, crepNestedSeqHOL]
    refine (bounded_seq (bounded_assign name (.loadGlob address)) (ih (address + 1))).mono ?_
    simp only [crepNodeWork]
    omega

theorem lookup_zip_not_mem {β : Type} (m : HolFiniteMapExact Nat β) (xs : List Nat)
    (ys : List β) (k : Nat) (hk : k ∉ xs) : (m.updateListEq (xs.zip ys)).lookup k = m.lookup k := by
  induction xs generalizing ys m with
  | nil => simp only [List.zip_nil_left]; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zip_nil_right]; rfl
    | cons y ys =>
      simp only [List.mem_cons, not_or] at hk
      rw [List.zip_cons_cons, updateListEq_cons_eq, ih _ _ hk.2]
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hk.1]

theorem handler_plan_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dest : Option (VarKind × MlStringHOL)} {handlerId handlerVar : MlStringHOL}
    {handlerProgram : ProgHOL 64} {returnShape : ShapeHOL}
    {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost entry : PanSemStateFiniteExact 64 F} {program : ProgHOL 64}
    (plan : callCostPlan s (some (dest, some (handlerId, handlerVar, handlerProgram)))
      returnShape bodyResult bodyPost = .handler entry program) :
    ∃ exn shape, bodyResult = some (.exception handlerId exn) ∧
      s.eshapes.lookup handlerId = some shape ∧
      shapeEqHOL (shapeOfHOLExact exn) shape = true ∧
      isValidValueHOLExact s.toExact .local handlerVar exn = true ∧
      entry = setVarHOLFinite handlerVar exn { bodyPost with locals := s.locals } ∧
      program = handlerProgram := by
  rcases bodyResult with _ | r
  · simp [callCostPlan] at plan
  cases r with
  | returned v =>
    simp only [callCostPlan] at plan
    repeat' split at plan
    all_goals simp at plan
  | exception eid v =>
    simp only [callCostPlan] at plan
    split at plan
    · rename_i same
      subst same
      split at plan
      · rename_i shape hshape
        split at plan
        · rename_i ok
          obtain ⟨hsh, hvalid⟩ := Bool.and_eq_true_iff.mp ok
          simp only [CallCostPlan.handler.injEq] at plan
          exact ⟨v, shape, rfl, hshape, hsh, hvalid, plan.1.symm, plan.2.symm⟩
        · simp at plan
      · simp at plan
    · simp at plan
  | _ => simp [callCostPlan] at plan

/-- Handler entry: `exp_hdl` copies the exception payload from globals into the
handler variable's slots, then the handler body runs under all original
simulation premises. Target locals may differ from the caller's above `vmax`
(compiled return slots). -/
theorem handler_entry_work {F : Type} {s bodyPost : PanSemStateFiniteExact 64 F}
    {context : PanToCrepContextExact 64} {t t1 : CrepSemHOLState 64 F}
    {handlerVar : MlStringHOL} {exn : ValueHOL 64} {handlerProgram : ProgHOL 64}
    {handlerEvents : List WorkEvent} (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (locals : panToCrepLocalsRelFiniteExact context s.locals t.locals)
    (agree : ∀ k, k ≤ context.vmax → targetLocals.lookup k = t.locals.lookup k)
    (valid : isValidValueHOLExact s.toExact .local handlerVar exn = true)
    (wellFormed : isWfShapeValueHOLExact [] exn = true)
    (globals : 1 ≤ sizeOfShapeHOL (shapeOfHOLExact exn) →
      globalsLookupHOL t1 exn = some (flattenHOL exn) ∧ sizeOfShapeHOL (shapeOfHOLExact exn) ≤ 32)
    (state : panToCrepStateRelFiniteExact bodyPost t1)
    (code : codeRelExactHOLW context bodyPost.code t1.code)
    (exceptions : panToCrepExcpRelFiniteExact context.eids bodyPost.eshapes)
    (ih : ∀ t', SourceCrepRel context
        (setVarHOLFinite handlerVar exn { bodyPost with locals := s.locals }) t' →
      CrepWorkPaid t' (compileProgExactHOLW context handlerProgram) handlerEvents) :
    ∃ w, CrepWork { t1 with locals := targetLocals }
        (.seq (expHdlExact context.vars handlerVar) (compileProgExactHOLW context handlerProgram)) w ∧
      w ≤ 2 + 3 * (flattenHOL exn).length +
        sourceCrepWeights.score (executionWork handlerEvents) := by
  classical
  cases hold : s.locals.lookup handlerVar with
  | none => simp [isValidValueHOLExact, lookupKvarHOLExact, hold] at valid
  | some old =>
  have hse : shapeOfHOLExact exn = shapeOfHOLExact old := by
    have : shapeEqHOL (shapeOfHOLExact exn) (shapeOfHOLExact old) = true := by
      simpa [isValidValueHOLExact, lookupKvarHOLExact, hold] using valid
    exact (shapeEqHOL_eq_true _ _).mp this
  obtain ⟨nsE, words, hvar, hmm, hfl, hwfo⟩ := locals.2.2 handlerVar old hold
  have hwfE : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact exn) = true := by
    rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl exn]
    exact wellFormed
  have hflenE := flattenHOL_length_eq_sizeOfShapeHOL exn hwfE
  have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
  have hnsE : nsE.length = (flattenHOL exn).length := by
    rw [opt_mmap_length_eq _ _ _ hmm, ← hfl, hflo, hflenE, hse]
  have hglobE : ((List.range nsE.length).map (fun i => (0 : BitVec 5) + BitVec.ofNat 5 i)).mapM
      t1.globals.lookup = some (flattenHOL exn) := by
    by_cases hz : sizeOfShapeHOL (shapeOfHOLExact exn) = 0
    · have h0 : nsE.length = 0 := by rw [hnsE, hflenE, hz]
      have hf0 : flattenHOL exn = [] := List.eq_nil_of_length_eq_zero (by rw [hflenE, hz])
      rw [h0, hf0]; rfl
    · have hg := (globals (by omega)).1
      rw [hnsE, hflenE]
      simpa [globalsLookupHOL] using hg
  have hndE : nsE.Nodup := locals.1.1 handlerVar _ nsE hvar
  have hlocTT := panToCrepLocalsRelFiniteExact_agreeBelowVmax context s.locals t.locals
    targetLocals locals agree
  obtain ⟨nsE', words', hvar', hmm', _, _⟩ := hlocTT.2.2 handlerVar old hold
  rw [hvar] at hvar'
  simp only [Option.some.injEq, Prod.mk.injEq] at hvar'
  obtain ⟨_, rfl⟩ := hvar'
  have hpresent : ∀ m, m ∈ nsE → targetLocals.lookup m ≠ none := by
    intro m hm
    have key : ∀ l : List Nat, ∀ ws, l.mapM targetLocals.lookup = some ws → ∀ m, m ∈ l →
        targetLocals.lookup m ≠ none := by
      intro l
      induction l with
      | nil => intro _ _ m hm; simp at hm
      | cons x xs ih =>
          intro ws hws m hm
          rw [List.mapM_cons] at hws
          cases hx : targetLocals.lookup x with
          | none => rw [hx] at hws; simp at hws
          | some wx =>
              cases hxs : xs.mapM targetLocals.lookup with
              | none => rw [hx, hxs] at hws; simp at hws
              | some wxs =>
                  rcases List.mem_cons.mp hm with rfl | hm'
                  · rw [hx]; simp
                  · exact ih wxs hxs m hm'
    exact key nsE words' hmm' m hm
  have hexp : (expHdlExact context.vars handlerVar : CrepProgHOL 64) =
      crepNestedSeqHOL (panMap2 (fun destination source => .assign destination source)
        nsE (loadGlobalsHOL 0 nsE.length)) := by
    simp [expHdlExact, hvar]
  have hrunExp := crepEvalAssignLoadGlobals nsE { t1 with locals := targetLocals } 0
    (flattenHOL exn) hndE hpresent hglobE
  have hsetE : panToCrepLocalsRelFiniteExact context
      (setVarHOLFinite handlerVar exn { bodyPost with locals := s.locals }).locals
      (targetLocals.updateListEq (nsE.zip (flattenHOL exn))) := by
    have hvarE : context.vars.lookup handlerVar = some (shapeOfHOLExact exn, nsE) := by
      rw [hvar, hse]
    have hlr := panToCrepLocalsRelFiniteExact_setVar context s.locals targetLocals handlerVar exn
      nsE hlocTT hvarE hnsE hwfE
    have hupd : s.locals.update (handlerVar, exn) = s.locals.updateEq (handlerVar, exn) := by
      apply HolFiniteMapExact.ext
      funext k
      simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL_eq_FUPDATE]
    simpa [setVarHOLFinite, hupd] using hlr
  obtain ⟨wh, workHandler, boundHandler⟩ :=
    ih ({ t1 with locals := targetLocals.updateListEq (nsE.zip (flattenHOL exn)) } :
      CrepSemHOLState 64 F) ⟨by simpa [panToCrepStateRelFiniteExact, setVarHOLFinite] using state, code, exceptions,
      hsetE⟩
  obtain ⟨we, workExp, boundExp⟩ := bounded_load_globals nsE 0 F { t1 with locals := targetLocals }
  rw [← hexp] at workExp hrunExp
  refine ⟨1 + we + wh, CrepWork.seqNext workExp hrunExp workHandler, ?_⟩
  rw [hnsE] at boundExp
  omega

theorem call_handler_events_score (arguments bodyEvents handlerEvents : List WorkEvent)
    (a b f c : Nat) :
    sourceCrepWeights.score (executionWork (.statement :: (arguments ++ [.copy a, .frame b, .frame f] ++
      bodyEvents ++ [.copy c] ++ handlerEvents))) =
    8 + sourceCrepWeights.score (executionWork arguments) + 8 * a + 8 * b + 8 * f +
      sourceCrepWeights.score (executionWork bodyEvents) + 8 * c +
      sourceCrepWeights.score (executionWork handlerEvents) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, score_append,
    executionWork_score_cons]
  simp only [executionWork, WorkEvent.units, Work.score, sourceCrepWeights]
  omega

/-- Caught exceptions: the callee body, payload copy into the handler variable
and the handler body are all charged to their actual source events. -/
theorem call_handler_transfer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {t : CrepSemHOLState 64 F} {context : PanToCrepContextExact 64}
    {info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64))}
    {function : MlStringHOL} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlStringHOL (ValueHOL 64)}
    {returnShape : ShapeHOL} {bodyResult : Option (PanSemResultExact 64)}
    {bodyPost handlerEntry : PanSemStateFiniteExact 64 F} {handlerProgram : ProgHOL 64}
    {bodyEvents handlerEvents : List WorkEvent}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler handlerEntry handlerProgram)
    (rel : SourceCrepRel context s t)
    (localised : localisedProgHOL (.call info function arguments) = true)
    (checkedArgs : bulkLoadSitesExps arguments = true)
    (ihBody : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' (callEntryStateHOLFinite s callee) t' →
      localisedProgHOL body = true →
      CrepWorkPaid t' (compileProgExactHOLW context' body) bodyEvents)
    (ihHandler : ∀ (t' : CrepSemHOLState 64 F) (context' : PanToCrepContextExact 64),
      SourceCrepRel context' handlerEntry t' →
      localisedProgHOL handlerProgram = true →
      CrepWorkPaid t' (compileProgExactHOLW context' handlerProgram) handlerEvents) :
    CrepWorkPaid t (compileProgExactHOLW context (.call info function arguments))
      (.statement :: (expressionListEvents s arguments ++
        [.copy (values.flatMap flattenHOL).length, .frame values.length,
          .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
        [.copy (callPayloadWords bodyResult)] ++ handlerEvents)) := by
  classical
  obtain ⟨dest, handlerId, handlerVar, rfl⟩ := handler_plan_info plan
  obtain ⟨exn, shape, rfl, _, _, valid, rfl, -⟩ := handler_plan_inv plan
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode', hexcp',
    hloc'⟩ :=
    pcCompileCorrectCallPrelude s t context function arguments values body callee returnShape
      args lookup rel.state rel.code rel.exceptions rel.locals (everyArgs_localised localised)
  obtain ⟨wb, workBody, boundBody⟩ := ihBody _ _ ⟨hst', hcode', hexcp', hloc'⟩ hprogLoc
  obtain ⟨r1, t1, hrun1, hs, hc, he, hrr⟩ :=
    compiled_source_run _ _ bodyRun.sound (by simp) hst' hcode' hexcp' hloc' hprogLoc
  simp only [pcCompileCorrectResultRel, ctxtFcExactHOL] at hrr
  cases hn : context.eids.lookup handlerId with
  | none => rw [hn] at hrr; exact hrr.elim
  | some n =>
  rw [hn] at hrr
  obtain ⟨rfl, hglob⟩ := hrr
  have hwfvE : isWfShapeValueHOLExact [] exn = true := by
    have := panToCrepFiniteEvaluateShapeInvariantRetInst2 arguments s function values body
      callee returnShape body (.exception handlerId exn) bodyPost t context t.locals
      (by simpa [evalListHOLFiniteClassical] using args)
      (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ lookup) bodyRun.sound
      rel.state rel.locals
    simpa using this
  have hlocP : localisedProgHOL handlerProgram = true := by
    rcases dest with _ | ⟨k, nm⟩ <;> (try rcases k) <;> simp_all [localisedProgHOL]
  have hfire : compileCallHdlC context (some (handlerId, handlerVar, handlerProgram)) =
      some (n, CrepProgHOL.seq (expHdlExact context.vars handlerVar)
        (compileProgExactHOLW context handlerProgram)) := by
    simp [compileCallHdlC, hn]
  have handlerWork := fun (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
      (agree : ∀ k, k ≤ context.vmax → targetLocals.lookup k = t.locals.lookup k) =>
    handler_entry_work (s := s) (t := t) (t1 := t1) (handlerProgram := handlerProgram)
      (handlerEvents := handlerEvents) targetLocals rel.locals agree valid hwfvE hglob hs
      (codeRelExactHOLW_ctxtFc context _ _ _ _ _ hc) he
      (fun t' rel' => ihHandler t' context rel' hlocP)
  have htclock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
  have argsPaid := arguments_paid rel arguments values args checkedArgs
  have rsize := frame_size_eq rel returnShape
  unfold CrepWorkPaid
  rw [call_handler_events_score, rsize]
  simp only [callPayloadWords]
  generalize sourceCrepWeights.score (executionWork (expressionListEvents s arguments)) = A
    at argsPaid ⊢
  generalize sourceCrepWeights.score (executionWork bodyEvents) = B at boundBody ⊢
  generalize sourceCrepWeights.score (executionWork handlerEvents) = H at handlerWork ⊢
  rcases compileCallSomeShapeHdl context dest (some (handlerId, handlerVar, handlerProgram))
      function arguments vshapes returnShape rel.locals.1 hfuncs with hc | ⟨_, hnone⟩ | ⟨rts0, hnd0, hc⟩
  · rw [hc, hfire]
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
    obtain ⟨wh, workH, boundH⟩ := handlerWork
      (zeroSlotState t ((List.range (sizeOfShapeHOL returnShape)).map
        (fun i => context.vmax + i + 1))).locals (by
        intro k hk
        simp only [zeroSlotState]
        apply lookup_zip_not_mem
        simp only [List.mem_map, List.mem_range, not_exists, not_and]
        intro i _ heq
        omega)
    have inner := CrepWork.callHandler (t := zeroSlotState t _) zeroArgs htlookup hnodup htclock
      workBody hrun1 workH
    refine ⟨_, work_zero_slots t _ _ _ hnodup inner, ?_⟩
    simp only [List.length_map, List.length_range]
    omega
  · rw [hfire] at hnone; exact absurd hnone (by simp)
  · rw [hc, hfire]
    obtain ⟨wh, workH, boundH⟩ := handlerWork t.locals (fun _ _ => rfl)
    exact ⟨_, CrepWork.callHandler htargs htlookup hnd0 htclock workBody hrun1 workH, by omega⟩

#print axioms call_handler_transfer
#print axioms bounded_load_globals
#print axioms handler_plan_inv
#print axioms handler_entry_work
end InitECandidate.Runtime.FineCost
