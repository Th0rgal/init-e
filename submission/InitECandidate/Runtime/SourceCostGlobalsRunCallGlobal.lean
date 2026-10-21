import InitECandidate.Runtime.SourceCostGlobalsRunCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! A call into a global: `pan_globals` declares the temporary at the global's
shape around the call and stores it back to the `TopAddr` slot. -/

theorem globals_compile_call_global (context : PanGlobalsContextExact 64) (name function : MlStringHOL)
    (arguments : List (ExpHOL 64)) {shape address}
    (found : context.globals.lookup name = some (shape, address)) :
    compileProgExactHOL context (.call (some (some (.global, name), none)) function arguments) =
      .decCall globalsTemp shape function (compileExpExactHOLList context arguments)
        (.store (.op .sub [.topAddr, .const address]) (.var .local globalsTemp)) := by
  simp [compileProgExactHOL, found, globalsTemp]

theorem globals_compile_call_missing (context : PanGlobalsContextExact 64) (name function : MlStringHOL)
    (arguments : List (ExpHOL 64)) (missing : context.globals.lookup name = none) :
    compileProgExactHOL context (.call (some (some (.global, name), none)) function arguments) =
      .call (some (none, none)) function (compileExpExactHOLList context arguments) := by
  simp [compileProgExactHOL, missing]

/-- A laid-out global is present in the source with the laid-out shape. -/
theorem globals_global_entry {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    (cov : GlobalsCovered context s) {name shape address}
    (found : context.globals.lookup name = some (shape, address)) :
    ∃ old, s.globals.lookup name = some old ∧ shape = shapeOfHOLExact old ∧
      sizeOfShapeWithContextHOL t.structs shape = (flattenHOL old).length ∧
      sizeOfShapeWithContextHOL s.structs shape = (flattenHOL old).length := by
  have present := cov name _ found
  unfold GlobalsPresent at present
  rcases hold : s.globals.lookup name with _ | old
  · exact absurd hold present
  obtain ⟨address', found', wf⟩ := globalsRel_global rel hold
  rw [found] at found'
  simp only [Option.some.injEq, Prod.mk.injEq] at found'
  obtain ⟨rfl, -⟩ := found'
  have length := flattenHOL_length_eq_sizeOfShapeHOL old wf
  have structs := panGlobalsStateRelStructsHOLExact b context s t rel
  refine ⟨old, rfl, rfl, ?_, ?_⟩
  · rw [structs.2, sharp_size_nil, length]
  · rw [structs.1, sharp_size_nil, length]

theorem globals_callGlobal_global {F : Type} {s : PanSemStateFiniteExact 64 F} {name} {old : ValueHOL 64}
    (hold : s.globals.lookup name = some old) :
    callGlobalEvents s (some (some (.global, name), none)) = [.globalAccess (flattenHOL old).length] := by
  simp [callGlobalEvents, globalEvents, hold]

theorem globals_temp_store_events (B : Nat) {F : Type} {u : PanSemStateFiniteExact 64 F}
    {address word : BitVec 64} {value value' : ValueHOL 64} {aev vev : List WorkEvent}
    (dst : CostedExpressionRun u (.op .sub [.topAddr, .const address]) (some (.val (.word word))) aev)
    (src : CostedExpressionRun u (.var .local globalsTemp) (some value') vev)
    (bound : u.locals.lookup globalsTemp = some value) :
    sharpSourceScore B (.statement :: (aev ++ vev ++ [.memory (flattenHOL value').length,
      .cost (storeOverhead (flattenHOL value').length)])) ≤
      globalAddressPrice + 156 * (flattenHOL value).length := by
  have read : expressionValue u (.var .local globalsTemp) = some value := by
    simpa [expressionValue, evalHOLExact] using bound
  have hv : value' = value := Option.some.inj (src.sound.symm.trans read)
  subst hv
  have addr := globals_address_events B dst
  have price : sourcePrice u (.var .local globalsTemp) = 14 * (flattenHOL value').length := by
    simp [sourcePrice, sourcePrices, exprPrices, valueInfo, bound]; omega
  rw [src.events_eq, srcScore_statement, sharpSourceScore_append, sharpSourceScore_append,
    srcScore_expressionEvents, price]
  gsimp
  omega

/-- The temporary's store back to the global slot. -/
theorem globals_temp_store_score (B : Nat) {F : Type} {u post : PanSemStateFiniteExact 64 F}
    {address : BitVec 64} {r ev} {value : ValueHOL 64}
    (run : StatementRun fn u (.store (.op .sub [.topAddr, .const address]) (.var .local globalsTemp)) r post ev)
    (ok : r ≠ some .error) (bound : u.locals.lookup globalsTemp = some value) :
    sharpSourceScore B ev ≤ globalAddressPrice + 156 * (flattenHOL value).length := by
  cases run
  case storeValue => exact globals_temp_store_events B (by assumption) (by assumption) bound
  all_goals exact absurd rfl ok

theorem globals_callDone_global (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name function arguments values body callee returnShape bodyResult bodyPost bodyEvents result}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun function (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s (some (some (.global, name), none)) returnShape bodyResult bodyPost =
      .done result post)
    (ihBody : GlobalsLe function B (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents) :
    GlobalsLe fn B s (.call (some (some (.global, name), none)) function arguments) result post
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape) +
            callMoves fn function)] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)] ++
        callGlobalEvents s (some (some (.global, name), none)))) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.callDone args lookup clock bodyRun plan) ok rel target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments (globals_ready_call_args ready) (globals_args_ok args)
  have bodyOk := globals_body_ok plan ok
  obtain ⟨readyBody, entryNoTemp, entryCode⟩ := globals_entry_ready code lookup
  have relEntry := globalsRel_callEntry rel callee
  have b := fun r p e (run : StatementRun function (callEntryStateHOLFinite t callee) (compileProgExactHOL context body) r p e) =>
    ihBody context _ relEntry bodyOk readyBody entryCode entryNoTemp cov r p e run
  cases found : context.globals.lookup name with
  | none =>
    rw [globals_compile_call_missing context name function arguments found] at target
    cases target
    case callDone =>
      rename_i vs body' callee' rs' br' bp' bev' clock' lookup' bodyRun' args' plan'
      have : vs = values := Option.some.inj (args'.symm.trans values')
      subst this
      obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
      subst hb hc hrs
      have bb := b _ _ _ bodyRun'
      obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
      subst hbr
      rw [globals_rel_structs rel]
      simp only [callGlobalEvents, srcScore_statement, sharpSourceScore_append,
        srcScore_copy, srcScore_frame, sharpSourceScore_nil]
      have nonneg := Nat.zero_le (sharpSourceScore B (globalEvents .global
        (((s.globals.lookup name).map (fun value => (flattenHOL value).length)).getD 0)))
      first
        | omega
        | (simp only [globalEvents, srcScore_global, sharpSourceScore_nil]; omega)
    case callHandler =>
      rename_i _ _ _ _ _ _ _ _ _ _ _ plan' _ _ _ _
      obtain ⟨_, _, _, hinfo⟩ := globals_plan_handler_info plan'
      cases hinfo
    case callTimeout =>
      rename_i _ _ _ _ clock' _ _
      have := globalsRel_clock rel
      omega
    all_goals (cases hr; try exact absurd rfl ok)
  | some entry =>
    obtain ⟨shape, address⟩ := entry
    obtain ⟨old, hold, rfl, sizeT, sizeS⟩ := globals_global_entry rel cov found
    rw [globals_compile_call_global context name function arguments found] at target
    rw [globals_callGlobal_global hold]
    cases target
    case declareCallReturn =>
      rename_i vs body' callee' rs' v bp' bev' cev post' clock' shapeMatch' lookup' bodyRun' args'
        contRun'
      have : vs = values := Option.some.inj (args'.symm.trans values')
      subst this
      obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
      subst hb hc hrs
      have bb := b _ _ _ bodyRun'
      obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
      subst hbr
      simp only [Bool.and_eq_true, shapeEqHOL_eq_true] at shapeMatch'
      obtain ⟨hshape, hreturn⟩ := shapeMatch'
      have hsize : (flattenHOL v).length = (flattenHOL old).length := by
        rw [← sizeS, ← hshape]
        have := globals_global_entry rel cov found
        obtain ⟨old', hold', hs', _, sizeS'⟩ := this
        rw [hold] at hold'
        cases hold'
        have wf := (globalsRel_global rel hold).choose_spec.2
        rw [← hshape] at wf
        rw [panGlobalsStateRelStructsHOLExact true context s t rel |>.1, sharp_size_nil]
        exact flattenHOL_length_eq_sizeOfShapeHOL v wf
      have cont := globals_temp_store_score B contRun' (by rw [hr]; exact ok)
        (value := v) (by simp [setVarHOLFinite, FUPDATE])
      have tempOld : t.locals.lookup globalsTemp = none := by rw [← globalsRel_locals rel]; exact h
      rw [← hreturn, hshape, sizeT, sizeS, ← hsize]
      simp only [callExitOverhead, callPayloadWords, Option.map_none, Option.getD_none]
      gsimp
      simp only [globalAddressPrice] at cont
      omega
    case declareCallStopped =>
      rename_i vs body' callee' rs' br' bp' bev' terminal' clock' lookup' bodyRun' args'
      have : vs = values := Option.some.inj (args'.symm.trans values')
      subst this
      obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
      subst hb hc hrs
      have bb := b _ _ _ bodyRun'
      obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
      subst hbr
      rw [sizeT]
      gsimp
      omega
    case declareCallTimeout =>
      rename_i _ _ _ _ clock' _ _
      have := globalsRel_clock rel
      omega
    all_goals (cases hr; try exact absurd rfl ok)

#print axioms globals_callDone_global
end InitECandidate.Runtime.FineCost
