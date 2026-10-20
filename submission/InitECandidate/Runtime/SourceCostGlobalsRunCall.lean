import InitECandidate.Runtime.SourceCostGlobalsCallBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A call destination that `pan_globals` leaves in place. -/
def globalsPlainInfo :
    Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64)) → Bool
  | some (some (.global, _), _) => false
  | _ => true

theorem globals_compile_call_plain (context : PanGlobalsContextExact 64) {info} (function : MlStringHOL)
    (arguments : List (ExpHOL 64)) (plain : globalsPlainInfo info = true) :
    compileProgExactHOL context (.call info function arguments) =
      .call (globalsMapInfo context info) function (compileExpExactHOLList context arguments) := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨exception, handlerVar, handler⟩⟩
  all_goals (try cases kind)
  all_goals first
    | (simp [compileProgExactHOL, globalsMapInfo]; done)
    | (simp [globalsPlainInfo] at plain)

theorem globals_ready_call_args {info function} {arguments : List (ExpHOL 64)}
    (ready : globalsReadyProg (.call info function arguments) = true) :
    globalsReadyExps arguments = true := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨exception, handlerVar, handler⟩⟩
  all_goals (try cases kind)
  all_goals (simp only [globalsReadyProg, Bool.and_eq_true] at ready)
  all_goals first | exact ready | exact ready.1 | simp at ready

theorem globals_callGlobal_plain {F : Type} (context : PanGlobalsContextExact 64)
    (t : PanSemStateFiniteExact 64 F) {info} (plain : globalsPlainInfo info = true) :
    callGlobalEvents t (globalsMapInfo context info) = [] := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨exception, handlerVar, handler⟩⟩
  all_goals (try cases kind)
  all_goals first | rfl | simp [globalsPlainInfo] at plain

theorem globals_args_ok {F : Type} {s : PanSemStateFiniteExact 64 F} {arguments : List (ExpHOL 64)}
    {values : List (ValueHOL 64)}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values) :
    @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arguments ≠ none := by
  intro hn
  have : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = none := hn
  rw [args] at this
  cases this

theorem globals_rel_structs {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    (shape : ShapeHOL) :
    sizeOfShapeWithContextHOL t.structs shape = sizeOfShapeWithContextHOL s.structs shape := by
  have both := panGlobalsStateRelStructsHOLExact b context s t rel
  rw [both.1, both.2]

theorem globals_callDone_plain (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {info function arguments values body callee returnShape bodyResult bodyPost bodyEvents result}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (ihBody : GlobalsLe B (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plain : globalsPlainInfo info = true) :
    GlobalsLe B s (.call info function arguments) result post
      (.statement :: (expressionListEvents s arguments ++
        [.copy (values.flatMap flattenHOL).length, .frame values.length,
          .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
        [.copy (callPayloadWords bodyResult)] ++ callGlobalEvents s info)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.callDone args lookup clock bodyRun plan) ok rel target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments (globals_ready_call_args ready) (globals_args_ok args)
  have bodyOk := globals_body_ok plan ok
  obtain ⟨readyBody, entryNoTemp, entryCode⟩ := globals_entry_ready code lookup
  have relEntry := globalsRel_callEntry rel callee
  rw [globals_compile_call_plain context function arguments plain] at target
  cases target
  case callDone =>
    rename_i vs body' callee' rs' br' bp' bev' clock' bodyRun' lookup' args' plan'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    have b := ihBody context _ relEntry bodyOk readyBody entryCode entryNoTemp cov _ _ _ bodyRun'
    obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    subst hbr
    rw [globals_callGlobal_plain context t plain, globals_rel_structs rel]
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_copy, srcScore_frame,
      sharpSourceScore_nil]
    omega
  case callHandler =>
    rename_i vs body' callee' rs' br' bp' bev' entry' program' hev' clock' bodyRun' plan' lookup' args' _
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    obtain ⟨hbr, -⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    subst hbr
    obtain ⟨e, p, hp⟩ := globals_plan_handler_back (bodyPost := bodyPost) rel plan'
    rw [plan] at hp
    cases hp
  case callTimeout =>
    rename_i _ _ _ _ clock' _ _
    have := globalsRel_clock rel
    omega
  all_goals (cases hr; try exact absurd rfl ok)

#print axioms globals_callDone_plain
theorem globals_callHandler_plain (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {info function arguments values body callee returnShape bodyResult bodyPost bodyEvents
      handlerEntry handlerProgram handlerEvents result}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler handlerEntry handlerProgram)
    (handlerRun : StatementRun handlerEntry handlerProgram result post handlerEvents)
    (ihBody : GlobalsLe B (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (ihHandler : GlobalsLe B handlerEntry handlerProgram result post handlerEvents)
    (plain : globalsPlainInfo info = true) :
    GlobalsLe B s (.call info function arguments) result post
      (.statement :: (expressionListEvents s arguments ++
        [.copy (values.flatMap flattenHOL).length, .frame values.length,
          .frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ bodyEvents ++
        [.copy (callPayloadWords bodyResult)] ++ handlerEvents)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  obtain ⟨hr, -⟩ := globals_sub_match
    (StatementRun.callHandler args lookup clock bodyRun plan handlerRun) ok rel target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments (globals_ready_call_args ready) (globals_args_ok args)
  have bodyOk := globals_body_ok_handler plan
  obtain ⟨readyBody, entryNoTemp, entryCode⟩ := globals_entry_ready code lookup
  have relEntry := globalsRel_callEntry rel callee
  rw [globals_compile_call_plain context function arguments plain] at target
  cases target
  case callDone =>
    rename_i vs body' callee' rs' br' bp' bev' clock' bodyRun' lookup' args' plan'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    obtain ⟨hbr, relBody⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    subst hbr
    obtain ⟨e', hplan, _⟩ := globals_plan_handler_match rel relBody plan
    rw [hplan] at plan'
    cases plan'
  case callHandler =>
    rename_i vs body' callee' rs' br' bp' bev' entry' program' hev' clock' bodyRun' plan' lookup' args'
      handlerRun'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    have b := ihBody context _ relEntry bodyOk readyBody entryCode entryNoTemp cov _ _ _ bodyRun'
    obtain ⟨hbr, relBody⟩ := globals_sub_match bodyRun bodyOk relEntry bodyRun'
    subst hbr
    obtain ⟨e', hplan, relE⟩ := globals_plan_handler_match rel relBody plan
    rw [hplan] at plan'
    cases plan'
    have hh := ihHandler context _ relE ok (globals_plan_handler_ready ready plan)
      (by rw [globals_plan_handler_code plan, bodyRun.code_eq]; exact code)
      (globals_plan_handler_noTemp plan h)
      (fun n e f => globals_plan_handler_present plan (bodyRun.covered cov n e f)) _ _ _ handlerRun'
    rw [globals_rel_structs rel]
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_copy, srcScore_frame,
      sharpSourceScore_nil]
    omega
  case callTimeout =>
    rename_i _ _ _ _ clock' _ _
    have := globalsRel_clock rel
    omega
  all_goals (cases hr; try exact absurd rfl ok)

theorem globals_callTimeout_plain (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {info function arguments values body callee returnShape}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0) (plain : globalsPlainInfo info = true) :
    GlobalsLe B s (.call info function arguments) (some .timeOut) (emptyLocalsHOLFinite s)
      (.statement :: (expressionListEvents s arguments ++
        [.frame (sizeOfShapeWithContextHOL s.structs returnShape)] ++ callGlobalEvents s info)) := by
  intro context t rel ok ready code h cov r' t' ev' target
  have values' := globals_list_values rel arguments values args
  have listLe := globals_list_le B rel arguments (globals_ready_call_args ready) (globals_args_ok args)
  have clockEq := globalsRel_clock rel
  obtain ⟨hr, -⟩ := globals_sub_match (StatementRun.callTimeout (info := info) args lookup clock) ok rel target
  rw [globals_compile_call_plain context function arguments plain] at target
  cases target
  case callTimeout =>
    rename_i vs body' callee' rs' clock' lookup' args'
    have : vs = values := Option.some.inj (args'.symm.trans values')
    subst this
    obtain ⟨hb, hc, hrs⟩ := globals_lookup_match rel lookup lookup'
    subst hb hc hrs
    rw [globals_callGlobal_plain context t plain, globals_rel_structs rel]
    simp only [srcScore_statement, sharpSourceScore_append, srcScore_frame, sharpSourceScore_nil]
    omega
  case callDone => rename_i _ _ _ _ _ _ _ clock' _ _ _ _; omega
  case callHandler => rename_i _ _ _ _ _ _ _ _ _ _ clock' _ _ _ _ _; omega
  all_goals (cases hr)

#print axioms globals_callHandler_plain
#print axioms globals_callTimeout_plain
end InitECandidate.Runtime.FineCost
