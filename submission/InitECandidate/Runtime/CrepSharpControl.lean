import InitECandidate.Runtime.CrepSharpAtomic
import InitECandidate.Runtime.CrepSharpWidth
import InitECandidate.Runtime.SourceCostSharpCrepControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

namespace SharpModel
variable (M : SharpModel) {fn : Flapjack.Pancake.PanLang.MlS}

theorem guard_paid {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {condition : ExpHOL 64} {word : BitVec 64}
    {guardEvents : List WorkEvent} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (guard : CostedExpressionRun s condition (some (.val (.word word))) guardEvents)
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL condition = true)
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    M.pr ce ≤ sharpScore guardEvents := by
  have bound := M.expression_paid s context t.locals rel.locals condition _
    guard.sound localised
  rw [compiled] at bound
  simp only [prs_cons, prs_nil] at bound
  rw [guard.events_eq]
  omega

theorem unit_paid {x : Nat} (h : x ≤ statementUnit) (e : Nat) :
    x ≤ sharpScore [.statement, .cost statementUnit] + e := by
  simp only [sharpScore_statement, sharpScore_cost, sharpScore_nil]; omega

/-- Work paid with a smaller one-off allowance is paid with a larger one. -/
theorem paid_mono {F : Type} {t : CrepSemHOLState 64 F} {program : CrepProgHOL 64}
    {events : List WorkEvent} {a b : Nat} (paid : M.CrepWorkPaidM (fn := fn) t program events a)
    (le : a ≤ b) : M.CrepWorkPaidM (fn := fn) t program events b := by
  obtain ⟨w, work, bound⟩ := paid
  exact ⟨w, work, by omega⟩

theorem stopP_stopPlan {F : Type} (bodyResult : Option (PanSemResultExact 64))
    (bodyPost : PanSemStateFiniteExact 64 F) :
    M.stopP bodyResult ≤ M.stopP (declareCallStopPlan bodyResult bodyPost).1 := by
  rcases bodyResult with _ | r
  · simp [stopP, declareCallStopPlan]
  · cases r <;> simp [stopP, declareCallStopPlan]

theorem expression_paid_run {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {value : ValueHOL 64}
    {events : List WorkEvent}
    (run : CostedExpressionRun s expression (some value) events)
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL expression = true) :
    M.prs (compileExpExactHOLW context expression).1 ≤
      sharpScore events := by
  have bound := M.expression_paid s context t.locals rel.locals expression _
    run.sound localised
  rw [run.events_eq]
  omega

theorem bounded_paid {F : Type} {t : CrepSemHOLState 64 F} {program : CrepProgHOL 64}
    {bound : Nat} {events : List WorkEvent} {e : Nat} (bounded : CrepBoundedM M program bound)
    (le : bound ≤ sharpScore events) :
    M.CrepWorkPaidM (fn := fn) t program events e := by
  obtain ⟨w, work, bw⟩ := bounded F fn t
  exact ⟨w, work, by omega⟩

/-- Control-statement transfer: sequential actual successors, selected
conditional branches, every loop guard and iteration, loop exits and timeouts.
Uses the full original Pan-to-Crep premises; the static guest load-site
certificate supplies the expression lowering bound. -/
theorem source_control_crep_work {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun fn s p r post events) :
    ∀ (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64),
      r ≠ some .error → SourceCrepRel context s t → localisedProgHOL p = true →
      sharpSitesProg sharpReplayBound p = true → sourceControlProg_sharp p = true →
      CodeCovered_sharp s.code → VarsSmall context → FuncsSmall context → widthProg p = true →
      CodeWidth s.code →
      M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context p) events (M.stopP r) := by
  have hBrk := M.breakOk; have hCont := M.contOk; have hTick := M.tickOk; have hIte := M.iteOk
  have hWh := M.whileOk
  simp only [whileOverhead, statementUnit] at hBrk hCont hTick hIte hWh
  induction run with
  | skip s =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨0, by simp only [compileProgExactHOLW]; exact CrepWorkF.skip _ t, Nat.zero_le _⟩
  | breakStmt s =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨_, by simp only [compileProgExactHOLW]; exact CrepWorkF.breakStmt _ t 0, unit_paid hBrk _⟩
  | continueStmt s =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨_, by simp only [compileProgExactHOLW]; exact CrepWorkF.continueStmt _ t 0, unit_paid hCont _⟩
  | tickStep clock =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨_, by simp only [compileProgExactHOLW]; exact CrepWorkF.tick _ t, unit_paid hTick _⟩
  | tickTimeout clock =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨_, by simp only [compileProgExactHOLW]; exact CrepWorkF.tick _ t, unit_paid hTick _⟩
  | annotation =>
    intro t context _ _ _ _ _ _ _ _ _ _
    exact ⟨0, by simp only [compileProgExactHOLW]; exact CrepWorkF.skip _ t, Nat.zero_le _⟩
  | @seqNext fn s first middle second r post left right one two ihOne ihTwo =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context (by simp) rel localised.1 checked.1 control.1 codeOk vs fs (by simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd; exact wd.1) cw
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run t context one.sound (by simp) rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨w2, work2, bound2⟩ :=
      ihTwo t1 context result ⟨state1, code1, exceptions1, locals1⟩ localised.2 checked.2
        control.2 (by rw [run_code_sharp one]; exact codeOk) vs fs (by simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd; exact wd.2)
        (by rw [run_code_sharp one]; exact cw)
    refine ⟨w1 + w2, by simp only [compileProgExactHOLW]; exact CrepWorkF.seqNext work1 run1 work2, ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at bound1 bound2 ⊢
    omega
  | @seqStop fn s first second r post left terminal one ihOne =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context result rel localised.1 checked.1 control.1 codeOk vs fs (by simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd; exact wd.1) cw
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run t context one.sound result rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨r0, rfl⟩ := Option.ne_none_iff_exists'.mp terminal
    obtain ⟨c1, rfl⟩ := Option.ne_none_iff_exists'.mp (resultRel_some_ne_none rel1)
    exact ⟨w1, by simp only [compileProgExactHOLW]; exact CrepWorkF.seqStop work1 run1, bound1⟩
  | @iteYes fn s condition yes no value guardEvents r post bodyEvents guard nonzero body ihBody =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := M.guard_paid guard rel localised.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.1.2 checked.1.2 control.1 codeOk vs fs (by simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd; exact wd.1) cw
    rw [compile_ite_eq_sharp context compiled]
    refine ⟨_, CrepWorkF.iteBranch (branchWork := wb) guardValue ?_, ?_⟩
    · rw [if_pos nonzero]; exact workBody
    · simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
      try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
      omega
  | @iteNo fn s condition yes no guardEvents r post bodyEvents guard body ihBody =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := M.guard_paid guard rel localised.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.2 checked.2 control.2 codeOk vs fs (by simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd; exact wd.2) cw
    rw [compile_ite_eq_sharp context compiled]
    refine ⟨_, CrepWorkF.iteBranch (branchWork := wb) guardValue ?_, ?_⟩
    · simpa using workBody
    · simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
      try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
      omega
  | @whileFalse fn s condition body guardEvents guard =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    rw [compile_while_eq_sharp context compiled]
    refine ⟨_, CrepWorkF.whileExit ?_, ?_⟩
    · intro word hw
      rw [guardValue] at hw
      simp only [Option.some.injEq, HolWordLab.word.injEq] at hw
      exact hw.symm
    · simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
      try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound ⊢
      omega
  | @whileTimeout fn s condition body value guardEvents guard nonzero clock =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    have targetClock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    rw [compile_while_eq_sharp context compiled]
    refine ⟨_, CrepWorkF.whileTimeout guardValue nonzero targetClock, ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound ⊢
    omega
  | @whileNext fn s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk vs fs
        (by simpa only [widthProg] using wd) cw
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole (by rw [run_code_sharp one]; exact codeOk) vs fs wd
        (by rw [run_code_sharp one]; exact cw)
    rw [compile_while_eq_sharp context compiled] at workRest ⊢
    refine ⟨_,
      CrepWorkF.whileLoop guardValue nonzero targetClock workBody run1 (Or.inl rfl) workRest, ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody boundRest ⊢
    omega
  | @whileContinue fn s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk vs fs
        (by simpa only [widthProg] using wd) cw
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole (by rw [run_code_sharp one]; exact codeOk) vs fs wd
        (by rw [run_code_sharp one]; exact cw)
    rw [compile_while_eq_sharp context compiled] at workRest ⊢
    refine ⟨_,
      CrepWorkF.whileLoop guardValue nonzero targetClock workBody run1 (Or.inr rfl) workRest, ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody boundRest ⊢
    omega
  | @whileBreak fn s condition body value guardEvents post bodyEvents guard nonzero clock one
      ihOne =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk vs fs
        (by simpa only [widthProg] using wd) cw
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, _⟩ := rel1
    rw [compile_while_eq_sharp context compiled]
    refine ⟨_,
      CrepWorkF.whileStop guardValue nonzero targetClock workBody run1 (by simp), ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
    omega
  | @whilePropagate fn s condition body value guardEvents post bodyEvents bodyResult guard nonzero
      clock notBreak notContinue one ihOne =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := M.guard_paid guard rel localised.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context result relBody localised.2 checked.2 control codeOk vs fs
        (by simpa only [widthProg] using wd) cw
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound result relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    rw [compile_while_eq_sharp context compiled]
    refine ⟨_,
      CrepWorkF.whileStop guardValue nonzero targetClock workBody run1
        ⟨resultRel_some_ne_none rel1, resultRel_not_continue notContinue rel1⟩, ?_⟩
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
    omega
  | @assignValue fn s kind name expression value events expr valid =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    cases kind with
    | «global» => simp [localisedProgHOL] at localised
    | «local» =>
      simp only [localisedProgHOL, sharpSitesProg] at localised checked
      have paid := M.expression_paid_run expr rel localised
      have length := compiled_length_sharp expr.sound rel localised
      simp only [compileProgExactHOLW]
      have cp := Nat.mul_le_mul_left (compileExpExactHOLW context expression).1.length M.copyOk
      refine M.bounded_paid (M.bounded_local_assign context name expression) ?_
      rw [length]
      simp only [globalEvents]
      simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
      try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
      try rw [length] at cp
      try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at cp
      omega
  | @storeValue fn s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := M.expression_paid_run dst rel localised.1
    have paidValue := M.expression_paid_run src rel localised.2
    have length := compiled_length_sharp src.sound rel localised.2
    simp only [compileProgExactHOLW]
    have so := M.storeOk (compileExpExactHOLW context source).1.length
    refine M.bounded_paid (M.bounded_store_compiled context destination source) ?_
    rw [length]
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    try rw [length] at so
    try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at so
    omega
  | @store32Value fn s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := M.expression_paid_run dst rel localised.1
    have paidValue := M.expression_paid_run src rel localised.2
    simp only [compileProgExactHOLW]
    have so := M.store32Ok
    refine M.bounded_paid (M.bounded_store32_compiled context destination source) ?_
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    try rw [length] at so
    try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at so
    omega
  | @storeByteValue fn s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := M.expression_paid_run dst rel localised.1
    have paidValue := M.expression_paid_run src rel localised.2
    simp only [compileProgExactHOLW]
    have so := M.store32Ok
    refine M.bounded_paid (M.bounded_storeByte_compiled context destination source) ?_
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    try rw [length] at so
    try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at so
    omega
  | @returnValue fn s expression value events expr size =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg] at localised checked
    have paid := M.expression_paid_run expr rel localised
    have length := compiled_length_sharp expr.sound rel localised
    simp only [compileProgExactHOLW]
    have r0 := M.returnOk 0
    have rn := M.returnOk (compileExpExactHOLW context expression).1.length
    refine M.bounded_paid (M.bounded_return_compiled context expression) ?_
    rw [length]
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
    try rw [length] at rn
    try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at r0 rn
    omega
  | @raiseValue fn s exceptionId expression value events shape expr declared shapeMatches size =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg] at localised checked
    have paid := M.expression_paid_run expr rel localised
    have length := compiled_length_sharp expr.sound rel localised
    simp only [compileProgExactHOLW]
    have ra := M.raiseOk (compileExpExactHOLW context expression).1.length
    refine M.bounded_paid (M.bounded_raise_compiled context exceptionId expression) ?_
    rw [length]
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
    try rw [length] at ra
    try simp only [returnOverhead, raiseOverhead, storeOverhead, statementUnit] at ra
    omega
  | @declareValue fn s name shape initializer body value initEvents bodyEvents result post init
      shapeMatch bodyRun ihBody =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    have paid := M.expression_paid_run init rel localised.1
    obtain ⟨bodyContext, bodyState, hctx, bodyFuncs, bodyRel, lift⟩ :=
      M.dec_transfer init.sound shapeMatch rel localised.1
    simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody bodyState bodyContext resultOk bodyRel localised.2 checked.2 control codeOk
        (by rw [hctx]; exact varsSmall_decCallCtxt vs name (by
          rw [← (shapeEqHOL_eq_true _ _).mp shapeMatch]; exact wd.1))
        (funcsSmall_of_funcs bodyFuncs fs) wd.2 (by exact cw)
    refine ⟨_, lift wb workBody, ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead]
    try simp only [stopP, sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_cost, sharpScore_nil, statementUnit, whileOverhead, returnOverhead, raiseOverhead, storeOverhead] at paid boundBody ⊢
    omega
  | @callDone fn s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents result post args lookup clock bodyRun plan ihBody =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have bodyOk := call_body_ok_sharp plan resultOk
    have checkedArgs : sharpSitesList sharpReplayBound arguments = true := by
      rcases info with _ | ⟨dest, _ | ⟨a, b, c⟩⟩ <;> simp_all [sharpSitesProg]
    rw [callGlobalEvents_localised localised, List.append_nil]
    exact M.call_done_transfer args lookup clock bodyRun plan resultOk rel vs fs localised checkedArgs
      (fun t' c' rel' loc' vs' fs' =>
        ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk vs' fs'
          (cw function vshapes body returnShape hsrc) cw)
  | @callTimeout fn s info function arguments values body callee returnShape args lookup clock =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    have checkedArgs : sharpSitesList sharpReplayBound arguments = true := by
      rcases info with _ | ⟨dest, _ | ⟨a, b, c⟩⟩ <;> simp_all [sharpSitesProg]
    rw [callGlobalEvents_localised localised, List.append_nil]
    exact M.call_timeout_transfer args lookup clock rel vs fs localised checkedArgs
  | @callHandler fn s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents handlerEntry handlerProgram handlerEvents result post args lookup clock bodyRun
      plan handlerRun ihBody ihHandler =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    obtain ⟨dest, exceptionId, handlerVar, rfl⟩ := handler_plan_info_sharp plan
    obtain ⟨exn, _, bodyException, _, _, _, entryEq, _⟩ := handler_plan_inv_sharp plan
    simp only [sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true] at checked control
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have bodyOk : bodyResult ≠ some .error := by rw [bodyException]; simp
    have handlerCode : CodeCovered_sharp handlerEntry.code := by
      rw [entryEq]
      show CodeCovered_sharp bodyPost.code
      rw [run_code_sharp bodyRun]
      exact codeOk
    have handlerCodeW : CodeWidth handlerEntry.code := by
      rw [entryEq]
      show CodeWidth bodyPost.code
      rw [run_code_sharp bodyRun]
      exact cw
    exact M.call_handler_transfer args lookup clock bodyRun plan rel vs fs localised checked.1
      (fun t' c' rel' loc' vs' fs' =>
        ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk vs' fs'
          (cw function vshapes body returnShape hsrc) cw)
      (fun t' c' rel' loc' vs' fs' =>
        ihHandler t' c' resultOk rel' loc' checked.2 control handlerCode vs' fs'
          (by simpa only [widthProg] using wd) handlerCodeW)
  | @declareCallReturn fn s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents continuationEvents result post args lookup clock bodyRun shapeMatch
      continuationRun ihBody ihContinuation =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    simp only [sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true] at checked control
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have localisedCont : localisedProgHOL continuation = true := by
      simp only [localisedProgHOL, Bool.and_eq_true] at localised; exact localised.2
    have contCode : CodeCovered_sharp (setVarHOLFinite name value
        { bodyPost with locals := s.locals }).code := by
      show CodeCovered_sharp bodyPost.code
      rw [run_code_sharp bodyRun]
      exact codeOk
    have contCodeW : CodeWidth (setVarHOLFinite name value
        { bodyPost with locals := s.locals }).code := by
      show CodeWidth bodyPost.code
      rw [run_code_sharp bodyRun]
      exact cw
    simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd
    exact M.decCall_return_transfer args lookup clock bodyRun shapeMatch rel vs fs wd.1 localised checked.1
      (fun t' c' rel' loc' vs' fs' => ihBody t' c' (by simp) rel' loc' bodyStatic.1 bodyStatic.2 codeOk
        vs' fs' (cw function vshapes body returnShape hsrc) cw)
      (fun t' c' rel' vs' fs' => ihContinuation t' c' resultOk rel' localisedCont checked.2 control
        contCode vs' fs' wd.2 contCodeW)
  | @declareCallTimeout fn s name shape function arguments continuation values body callee
      returnShape args lookup clock =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    simp only [sharpSitesProg, Bool.and_eq_true] at checked
    simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd
    exact M.decCall_timeout_transfer args lookup clock rel vs fs wd.1 localised checked.1
  | @declareCallStopped fn s name shape function arguments continuation values body callee
      returnShape bodyResult bodyPost bodyEvents args lookup clock bodyRun terminal ihBody =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    simp only [sharpSitesProg, Bool.and_eq_true] at checked
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have stop := decCall_stop_cases_sharp terminal resultOk
    have bodyOk : bodyResult ≠ some .error := by
      rcases stop with h | ⟨f, h⟩ | ⟨eid, v, h⟩ <;> rw [h] <;> simp
    simp only [widthProg, Bool.and_eq_true, decide_eq_true_eq] at wd
    exact M.paid_mono (M.decCall_stopped_transfer args lookup clock bodyRun stop rel vs fs wd.1 localised checked.1
      (fun t' c' rel' loc' vs' fs' => ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk
        vs' fs' (cw function vshapes body returnShape hsrc) cw))
      (M.stopP_stopPlan _ _)
  | @primitiveValue fn s name operator arguments values value args operation valid =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    simp only [sharpSitesProg] at checked
    exact M.paid_mono (M.primitive_transfer args operation valid rel localised checked) (Nat.zero_le _)
  | @external fn s function configuration configurationLength array arrayLength result post run =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    exact M.paid_mono (M.external_transfer run resultOk rel localised checked) (Nat.zero_le _)
  | @sharedLoad fn s operator kind name address result post run =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    exact M.paid_mono (M.shared_load_transfer run resultOk rel localised checked) (Nat.zero_le _)
  | @sharedStore fn s operator address value result post run =>
    intro t context resultOk rel localised checked control codeOk vs fs wd cw
    exact M.paid_mono (M.shared_store_transfer run resultOk rel localised checked) (Nat.zero_le _)
  | _ =>
    intro t context result rel localised checked control codeOk vs fs wd cw
    first
      | exact absurd rfl result
      | (simp [sourceControlProg_sharp] at control)


/-- Executed source-to-Crep work transfer for every exact source trace.
Premises: the exact source trace and a non-error result, the four original
`pc_compile_correct` relations, `localised_prog`, and the static guest
load-site certificate on the program and every function body. The compiled
Crep program's actual execution has a work derivation paid by the source
event vector under `sourceCrepWeights`. -/
theorem source_crep_executed_work {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun fn s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → sharpSitesProg sharpReplayBound body = true)
    (small : VarsSmall context) (fsmall : FuncsSmall context) (width : widthProg p = true)
    (codeWidth : CodeWidth s.code) :
    M.CrepWorkPaidM (fn := fn) t (compileProgExactHOLW context p) events (M.stopP r) := by
  refine M.source_control_crep_work run t context resultOk rel localised checked
    (covered_of_localised_sharp p localised) ?_ small fsmall width codeWidth
  intro function shapes body returnShape lookup
  obtain ⟨bodyLocalised, _, _⟩ := codeRelExactHOLW_imp context s.code t.code rel.code function
    shapes body returnShape lookup
  exact ⟨codeChecked function shapes body returnShape lookup,
    covered_of_localised_sharp body bodyLocalised⟩

/-- Selected-trace form: the canonical source execution cost pays for the
compiled Crep execution. -/
theorem source_execution_cost_pays_crep {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64)
    (resultOk : (evaluateHOLFiniteState s p).1 ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → sharpSitesProg sharpReplayBound body = true)
    (small : VarsSmall context) (fsmall : FuncsSmall context) (width : widthProg p = true)
    (codeWidth : CodeWidth s.code) :
    ∃ w, CrepWorkM M fn t (compileProgExactHOLW context p) w ∧
      w ≤ sharpScore (sourceExecutionEvents fn s p) + M.shortP := by
  obtain ⟨w, work, bound⟩ := M.source_crep_executed_work (sourceExecutionEvents_run fn s p) t context
    resultOk rel localised checked codeChecked small fsmall width codeWidth
  exact ⟨w, work, Nat.le_trans bound (Nat.add_le_add_left (M.stopP_le _) _)⟩

end SharpModel

#print axioms SharpModel.source_control_crep_work
#print axioms SharpModel.source_crep_executed_work
#print axioms SharpModel.source_execution_cost_pays_crep
end InitECandidate.Runtime.FineCost
