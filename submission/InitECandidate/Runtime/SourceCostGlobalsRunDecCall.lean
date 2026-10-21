import InitECandidate.Runtime.SourceCostGlobalsRunCallGlobal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

theorem globals_callTimeout_global (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name function arguments values body callee returnShape}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0) :
    GlobalsLe fn B s (.call (some (some (.global, name), none)) function arguments) (some .timeOut)
      (emptyLocalsHOLFinite s)
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape) +
            (callMoves fn function + callSites fn function))] ++
        callGlobalEvents s (some (some (.global, name), none)))) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments (globals_ready_call_args ready) (globals_args_ok args)
  have clockEq := globalsRel_clock rel
  obtain ⟨hr, -⟩ := globals_sub_match
    (StatementRun.callTimeout (info := some (some (.global, name), none)) args lookup clock) ok rel target
  cases found : context.globals.lookup name with
  | none =>
    rw [globals_compile_call_missing context name function arguments found] at target
    cases target
    case callTimeout =>
      rename_i vs body' callee' rs' clock' lookup' args'
      have : vs = values := Option.some.inj (args'.symm.trans values')
      subst this
      obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
      subst hb hc hrs
      rw [globals_rel_structs rel]
      have nonneg := Nat.zero_le (sharpSourceScore B (callGlobalEvents s (some (some (.global, name), none))))
      simp only [callGlobalEvents, srcScore_statement, sharpSourceScore_append, srcScore_frame,
        sharpSourceScore_nil] at nonneg ⊢
      omega
    case callDone => rename_i _ _ _ _ _ _ _ clock' _ _ _ _; omega
    case callHandler => rename_i _ _ _ _ _ _ _ _ _ _ clock' _ _ _ _ _; omega
    all_goals (cases hr)
  | some entry =>
    obtain ⟨shape, address⟩ := entry
    obtain ⟨old, hold, rfl, sizeT, sizeS⟩ := globals_global_entry rel cov found
    rw [globals_compile_call_global context name function arguments found] at target
    rw [globals_callGlobal_global hold]
    cases target
    case declareCallTimeout =>
      rename_i vs body' callee' rs' clock' lookup' args'
      have : vs = values := Option.some.inj (args'.symm.trans values')
      subst this
      rw [sizeT]
      gsimp
      omega
    case declareCallReturn =>
      rename_i _ _ _ _ _ _ _ _ _ clock' _ _ _ _ _; omega
    case declareCallStopped =>
      rename_i _ _ _ _ _ _ _ _ clock' _ _ _; omega
    all_goals (cases hr)

#print axioms globals_callTimeout_global
theorem globals_compile_decCall (context : PanGlobalsContextExact 64) (name : MlStringHOL) (shape)
    (function : MlStringHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) :
    compileProgExactHOL context (.decCall name shape function arguments continuation) =
      .decCall name shape function (compileExpExactHOLList context arguments)
        (compileProgExactHOL context continuation) := by
  simp [compileProgExactHOL]

theorem globals_declareCallReturn (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name shape function arguments continuation values body callee returnShape value bodyPost
      bodyEvents continuationEvents result}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body
      (some (.returned value)) bodyPost bodyEvents)
    (shapeMatch : (shapeEqHOL (shapeOfHOLExact value) shape &&
      shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
    (continuationRun : StatementRun fn
      (setVarHOLFinite name value { bodyPost with locals := s.locals })
      continuation result post continuationEvents)
    (ihBody : GlobalsLe function B (callEntryStateHOLFinite s callee) body (some (.returned value)) bodyPost
      bodyEvents)
    (ihCont : GlobalsLe fn B (setVarHOLFinite name value { bodyPost with locals := s.locals })
      continuation result post continuationEvents) :
    GlobalsLe fn B s (.decCall name shape function arguments continuation) result
      { post with locals := HolFiniteMapExact.resVarEq post.locals (name, s.locals.lookup name) }
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))] ++ bodyEvents ++
        [.cost (returnCopy (flattenHOL value).length)] ++ continuationEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match
    (StatementRun.declareCallReturn args lookup clock bodyRun shapeMatch continuationRun) ok rel target
  simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments ready.1.2 (globals_args_ok args)
  obtain ⟨readyBody, entryNoTemp, entryCode⟩ := globals_entry_ready code lookup
  have relEntry := globalsRel_callEntry rel callee
  rw [globals_compile_decCall] at target
  cases target
  case declareCallReturn =>
    rename_i vs body' callee' rs' v bp' bev' cev post' clock' shapeMatch' lookup' bodyRun' args'
      contRun'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    have bb := ihBody context _ relEntry (by simp) readyBody entryCode entryNoTemp cov _ _ _ bodyRun'
    obtain ⟨hbr, relBody⟩ := globals_sub_match bodyRun (by simp) relEntry bodyRun'
    cases hbr
    have locals := globalsRel_locals rel
    have relCont : panGlobalsStateRelHOLExact true context
        (setVarHOLFinite name value { bodyPost with locals := s.locals })
        (setVarHOLFinite name value { bp' with locals := t.locals }) := by
      rw [← locals]; exact globalsRel_setVar (globalsRel_setLocals relBody s.locals) name value
    have cc := ihCont context _ relCont ok ready.2
      (by simp only [setVarHOLFinite]; rw [bodyRun.code_eq]; exact code)
      (globals_noTemp_setVar ready.1.1 _ h)
      (fun n e f => bodyRun.covered cov n e f) _ _ _ contRun'
    rw [globals_rel_structs rel]
    gsimp
    omega
  case declareCallStopped =>
    rename_i vs body' callee' rs' br' bp' bev' terminal' clock' lookup' bodyRun' args'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    obtain ⟨hbr, -⟩ := globals_sub_match bodyRun (by simp) relEntry bodyRun'
    exact absurd hbr (terminal' value)
  case declareCallTimeout =>
    rename_i _ _ _ _ clock' _ _
    have := globalsRel_clock rel
    omega
  all_goals (cases hr; try exact absurd rfl ok)

theorem globals_declareCallTimeout (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name shape function arguments continuation values body callee returnShape}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0) :
    GlobalsLe fn B s (.decCall name shape function arguments continuation)
      (some .timeOut) (emptyLocalsHOLFinite s) (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))])) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match
    (StatementRun.declareCallTimeout (name := name) (shape := shape) (continuation := continuation)
      args lookup clock) ok rel target
  simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
  have listLe := globals_list_le B rel arguments ready.1.2 (globals_args_ok args)
  have clockEq := globalsRel_clock rel
  rw [globals_compile_decCall] at target
  cases target
  case declareCallTimeout =>
    rename_i vs _ _ _ h1 h2 h3
    have values' := globals_list_values rel arguments values args
    have : vs = values := by
      first
        | exact Option.some.inj (h1.symm.trans values')
        | exact Option.some.inj (h2.symm.trans values')
        | exact Option.some.inj (h3.symm.trans values')
    subst this
    rw [globals_rel_structs rel]
    gsimp
    omega
  case declareCallReturn => rename_i _ _ _ _ _ _ _ _ _ clock' _ _ _ _ _; omega
  case declareCallStopped => rename_i _ _ _ _ _ _ _ _ clock' _ _ _; omega
  all_goals (cases hr)

theorem globals_declareCallStopped (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name shape function arguments continuation values body callee returnShape bodyResult bodyPost
      bodyEvents}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (terminal : ∀ value, bodyResult ≠ some (.returned value))
    (ihBody : GlobalsLe function B (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents) :
    GlobalsLe fn B s (.decCall name shape function arguments continuation)
      (declareCallStopPlan bodyResult bodyPost).1 (declareCallStopPlan bodyResult bodyPost).2
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs shape) +
            (callMoves fn function + callSites fn function))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)])) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match
    (StatementRun.declareCallStopped (name := name) (shape := shape) (continuation := continuation)
      args lookup clock bodyRun terminal) ok rel target
  simp only [globalsReadyProg, Bool.and_eq_true, bne_iff_ne] at ready
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments ready.1.2 (globals_args_ok args)
  obtain ⟨readyBody, entryNoTemp, entryCode⟩ := globals_entry_ready code lookup
  have relEntry := globalsRel_callEntry rel callee
  have bodyOk : bodyResult ≠ some .error := by
    rintro rfl; exact ok (by simp [declareCallStopPlan])
  rw [globals_compile_decCall] at target
  cases target
  case declareCallStopped =>
    rename_i vs body' callee' rs' br' bp' bev' terminal' clock' lookup' bodyRun' args'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    have bb := ihBody context _ relEntry bodyOk readyBody entryCode entryNoTemp cov _ _ _ bodyRun'
    obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    subst hbr
    rw [globals_rel_structs rel]
    gsimp
    omega
  case declareCallReturn =>
    rename_i vs body' callee' rs' v bp' bev' cev post' clock' shapeMatch' lookup' bodyRun' args'
      contRun'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    exact absurd hbr.symm (terminal v)
  case declareCallTimeout =>
    rename_i _ _ _ _ clock' _ _
    have := globalsRel_clock rel
    omega
  all_goals (first | exact absurd hr.symm ok | (cases hr; try exact absurd rfl ok))

#print axioms globals_declareCallReturn
#print axioms globals_declareCallTimeout
#print axioms globals_declareCallStopped
end InitECandidate.Runtime.FineCost
