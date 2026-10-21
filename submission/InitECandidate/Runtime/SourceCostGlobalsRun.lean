import InitECandidate.Runtime.SourceCostGlobalsRunExternal
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! The `pan_globals` statement transfer for every source run. -/

theorem globals_error (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {p ev} :
    GlobalsLe B s p (some .error) post ev := by
  intro _ _ _ ok
  exact absurd rfl ok

theorem globals_callDone_any (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {info function arguments values body callee returnShape bodyResult bodyPost bodyEvents result}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : StatementRun (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents)
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (ihBody : GlobalsLe B (callEntryStateHOLFinite s callee) body bodyResult bodyPost bodyEvents) :
    GlobalsLe B s (.call info function arguments) result post
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)] ++ callGlobalEvents s info)) := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨exception, handlerVar, handler⟩⟩
  all_goals (try cases kind)
  all_goals first
    | exact globals_callDone_plain B args lookup clock bodyRun plan ihBody rfl
    | exact globals_callDone_global B args lookup clock bodyRun plan ihBody
    | (intro _ _ _ _ ready; simp [globalsReadyProg] at ready)

theorem globals_callHandler_any (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F}
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
    (ihHandler : GlobalsLe B handlerEntry handlerProgram result post handlerEvents) :
    GlobalsLe B s (.call info function arguments) result post
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape))] ++ bodyEvents ++
        [.cost (callExitOverhead bodyResult)] ++ handlerEvents)) := by
  by_cases plain : globalsPlainInfo info = true
  · exact globals_callHandler_plain B args lookup clock bodyRun plan handlerRun ihBody ihHandler plain
  · intro _ _ _ _ ready
    obtain ⟨dest, exception, handlerVar, rfl⟩ := globals_plan_handler_info plan
    rcases dest with _ | ⟨kind, name⟩
    · simp [globalsPlainInfo] at plain
    · cases kind
      · simp [globalsPlainInfo] at plain
      · simp [globalsReadyProg] at ready

theorem globals_callTimeout_any (B : Nat) {F : Type} {s : PanSemStateFiniteExact 64 F}
    {info function arguments values body callee returnShape}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (clock : s.clock = 0) :
    GlobalsLe B s (.call info function arguments) (some .timeOut) (emptyLocalsHOLFinite s)
      (.statement :: (expressionListEvents s arguments ++
        [.cost (callOverhead (values.flatMap flattenHOL).length +
          slotOverhead (sizeOfShapeWithContextHOL s.structs returnShape))] ++ callGlobalEvents s info)) := by
  rcases info with _ | ⟨_ | ⟨kind, name⟩, _ | ⟨exception, handlerVar, handler⟩⟩
  all_goals (try cases kind)
  all_goals first
    | exact globals_callTimeout_plain B args lookup clock rfl
    | exact globals_callTimeout_global B args lookup clock
    | (intro _ _ _ _ ready; simp [globalsReadyProg] at ready)

/-- `pan_globals` statement transfer: from a related state, the compiled
program's run costs no more than the source run under `sharpSourceScore B`,
for every non-error source run of a ready program. -/
theorem globals_run_le (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) : GlobalsLe B s p r post ev := by
  induction run
  case skip s => exact globals_skip B s
  case seqNext one two ih1 ih2 => exact globals_seqNext B one two ih1 ih2
  case seqStop terminal one ih => exact globals_seqStop B terminal one ih
  case iteYes guard nonzero body ih => exact globals_iteYes B guard nonzero body ih
  case iteNo guard body ih => exact globals_iteNo B guard body ih
  case breakStmt s => exact globals_break B s
  case continueStmt s => exact globals_continue B s
  case whileFalse guard => exact globals_whileFalse B guard
  case whileNext guard nonzero clock one rest ih1 ih2 =>
    exact globals_whileNext B guard nonzero clock one rest ih1 ih2
  case whileContinue guard nonzero clock one rest ih1 ih2 =>
    exact globals_whileContinue B guard nonzero clock one rest ih1 ih2
  case whileBreak guard nonzero clock one ih => exact globals_whileBreak B guard nonzero clock one ih
  case whileTimeout guard nonzero clock => exact globals_whileTimeout B guard nonzero clock
  case whilePropagate guard nonzero clock notBreak notContinue one ih =>
    exact globals_whilePropagate B guard nonzero clock notBreak notContinue one ih
  case assignValue kind _ _ _ _ expr valid =>
    cases kind
    · exact globals_assignLocal B expr valid
    · exact globals_assignGlobal B expr valid
  case returnValue expr size => exact globals_returnValue B expr size
  case raiseValue expr declared shapeMatches size =>
    exact globals_raiseValue B expr declared shapeMatches size
  case storeValue dst src write => exact globals_storeValue B dst src write
  case store32Value dst src write => exact globals_store32Value B dst src write
  case storeByteValue dst src write => exact globals_storeByteValue B dst src write
  case declareValue init shapeMatch bodyRun ih => exact globals_declareValue B init shapeMatch bodyRun ih
  case callDone args lookup clock bodyRun plan ih =>
    exact globals_callDone_any B args lookup clock bodyRun plan ih
  case callHandler args lookup clock bodyRun plan handlerRun ihBody ihHandler =>
    exact globals_callHandler_any B args lookup clock bodyRun plan handlerRun ihBody ihHandler
  case callTimeout args lookup clock => exact globals_callTimeout_any B args lookup clock
  case declareCallReturn args lookup clock bodyRun shapeMatch contRun ihBody ihCont =>
    exact globals_declareCallReturn B args lookup clock bodyRun shapeMatch contRun ihBody ihCont
  case declareCallTimeout args lookup clock => exact globals_declareCallTimeout B args lookup clock
  case declareCallStopped args lookup clock bodyRun terminal ih =>
    exact globals_declareCallStopped B args lookup clock bodyRun terminal ih
  case tickStep s _ => exact globals_tick B s _ _
  case tickTimeout s _ => exact globals_tick B s _ _
  case annotation s tag text => exact globals_annotation B s tag text
  case primitiveValue args operation valid => exact globals_primitiveValue B args operation valid
  case external run => exact globals_external B run
  case sharedLoad run => exact globals_sharedLoad B run
  case sharedStore run => exact globals_sharedStore B run
  all_goals exact globals_error B

#print axioms globals_run_le

/-- `pan_globals` transfer with the compiled run: from a related state, the
compiled program has a canonical run with the same result, ending in a state
related by the original `compile_correct` relation, whose sharp score is at
most the source run's. -/
theorem globals_compile_run (B : Nat) {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) (ok : r ≠ some .error)
    (context : PanGlobalsContextExact 64) (t : PanSemStateFiniteExact 64 F)
    (rel : panGlobalsStateRelHOLExact true context s t) (ready : globalsReadyProg p = true)
    (code : GlobalsCodeReady s.code) (noTemp : s.locals.lookup globalsTemp = none)
    (cov : GlobalsCovered context s) :
    ∃ t' ev', StatementRun t (compileProgExactHOL context p) r t' ev' ∧
      panGlobalsStateRelHOLExact (goodResHOL r) context post t' ∧
      sharpSourceScore B ev' ≤ sharpSourceScore B ev := by
  obtain ⟨t', target, rel'⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL p s r context t post
    ⟨rel, run.sound, ok⟩
  obtain ⟨ev', trace⟩ := source_evaluation_cost_trace t (compileProgExactHOL context p)
  rw [target] at trace
  exact ⟨t', ev', trace, rel', globals_run_le B run context t rel ok ready code noTemp cov _ _ _ trace⟩

#print axioms globals_compile_run
end InitECandidate.Runtime.FineCost
