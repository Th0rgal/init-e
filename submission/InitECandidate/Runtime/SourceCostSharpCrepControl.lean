import InitECandidate.Runtime.SourceCostSharpCrepAtomic
import InitECandidate.Runtime.SourceCostCrepControl
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Source statements currently covered by the checked transfer. -/
def sourceControlProg_sharp : ProgHOL 64 → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign VarKind.«local» _ _ | .store _ _ | .store32 _ _ | .storeByte _ _ | .return _ | .raise _ _ => true
  | .seq first second => sourceControlProg_sharp first && sourceControlProg_sharp second
  | .ite _ yes no => sourceControlProg_sharp yes && sourceControlProg_sharp no
  | .while _ body => sourceControlProg_sharp body
  | .dec _ _ _ body => sourceControlProg_sharp body
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, _, handler))) _ _ => sourceControlProg_sharp handler
  | .decCall _ _ _ _ continuation => sourceControlProg_sharp continuation
  | .primitive _ _ _ | .extCall _ _ _ _ _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ => true
  | _ => false

/-- Static premise on every source function body reachable through calls. -/
def CodeCovered_sharp (code : HolFiniteMapExact MlStringHOL
    (List (MlStringHOL × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ function shapes body returnShape, code.lookup function = some (shapes, body, returnShape) →
    sharpSitesProg sharpReplayBound body = true ∧ sourceControlProg_sharp body = true

theorem run_code_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) : post.code = s.code := by
  have := SemInitSupport.eval_code s p
  rw [run.sound] at this
  exact this

theorem guard_paid_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {condition : ExpHOL 64} {word : BitVec 64}
    {guardEvents : List WorkEvent} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (guard : CostedExpressionRun s condition (some (.val (.word word))) guardEvents)
    (rel : SourceCrepRel context s t) (checked : sharpSites sharpReplayBound condition = true)
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    loopNodePrice ce ≤ sharpScore guardEvents := by
  have bound := compiled_expression_sharp_score s context t.locals rel.locals rel.state.2.2.2.1 condition _
    guard.sound checked
  rw [compiled] at bound
  simp only [sharpCrepList_cons, sharpCrepList_nil] at bound
  rw [guard.events_eq]
  omega

theorem leaf_paid_sharp : 2 ≤ sharpScore [.statement] := by
  simp [sharpScore_statement, sharpScore_nil]

theorem score_copy_sharp (n : Nat) : sharpScore ([.copy n]) = 5 * n := by
  simp [sharpScore_copy, sharpScore_nil]

theorem score_memory_sharp (n : Nat) :
    sharpScore ([.memory n]) = 12 * n + 45 * (n - 1) := by
  simp [sharpScore_memory, sharpScore_nil]

theorem expression_paid_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {value : ValueHOL 64}
    {events : List WorkEvent}
    (run : CostedExpressionRun s expression (some value) events)
    (rel : SourceCrepRel context s t) (checked : sharpSites sharpReplayBound expression = true) :
    sharpCrepList (compileExpExactHOLW context expression).1 ≤
      sharpScore events := by
  have bound := compiled_expression_sharp_score s context t.locals rel.locals rel.state.2.2.2.1 expression _
    run.sound checked
  rw [run.events_eq]
  exact bound

theorem compiled_length_sharp {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {value : ValueHOL 64}
    (evaluated : expressionValue s expression = some value)
    (rel : SourceCrepRel context s t) (localised : localisedExpHOL expression = true) :
    (compileExpExactHOLW context expression).1.length = (flattenHOL value).length := by
  classical
  rcases hc : compileExpExactHOLW context expression with ⟨es, sh⟩
  obtain ⟨hes, _, _, _⟩ :=
    @compileExpValRelHOL 64 F _ s
      (fun address => Classical.propDecidable (s.memaddrs address)) context t
      (fun address => Classical.propDecidable (t.memaddrs address))
      expression value es sh evaluated rel.state rel.code rel.locals localised hc
  have := congrArg List.length hes
  simpa using this

theorem sharp_bounded_paid_sharp {F : Type} {t : CrepSemHOLState 64 F} {program : CrepProgHOL 64}
    {bound : Nat} {events : List WorkEvent} (bounded : CrepBoundedS program bound)
    (le : bound ≤ sharpScore events) :
    CrepWorkPaid_sharp t program events := by
  obtain ⟨w, work, bw⟩ := bounded F t
  exact ⟨w, work, by omega⟩

theorem compile_ite_eq_sharp (context : PanToCrepContextExact 64) {condition : ExpHOL 64}
    {yes no : ProgHOL 64} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    compileProgExactHOLW context (.ite condition yes no) =
      .ite ce (compileProgExactHOLW context yes) (compileProgExactHOLW context no) := by
  simp only [compileProgExactHOLW, compileIfExactHOLW, compiled]

theorem compile_while_eq_sharp (context : PanToCrepContextExact 64) {condition : ExpHOL 64}
    {body : ProgHOL 64} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    compileProgExactHOLW context (.while condition body) =
      .while ce (compileProgExactHOLW context body) := by
  simp only [compileProgExactHOLW, compileWhileExactHOLW, compiled]

/-- Control-statement transfer: sequential actual successors, selected
conditional branches, every loop guard and iteration, loop exits and timeouts.
Uses the full original Pan-to-Crep premises; the static guest load-site
certificate supplies the expression lowering bound. -/
theorem source_control_crep_work_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) :
    ∀ (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64),
      r ≠ some .error → SourceCrepRel context s t → localisedProgHOL p = true →
      sharpSitesProg sharpReplayBound p = true → sourceControlProg_sharp p = true →
      CodeCovered_sharp s.code →
      CrepWorkPaid_sharp t (compileProgExactHOLW context p) events := by
  induction run with
  | skip s =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.skip t, leaf_paid_sharp⟩
  | breakStmt s =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.breakStmt t 0, leaf_paid_sharp⟩
  | continueStmt s =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.continueStmt t 0, leaf_paid_sharp⟩
  | tickStep clock =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.tick t, leaf_paid_sharp⟩
  | tickTimeout clock =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.tick t, leaf_paid_sharp⟩
  | annotation =>
    intro t context _ _ _ _ _ _
    exact ⟨2, by simp only [compileProgExactHOLW]; exact CrepWorkS.skip t, leaf_paid_sharp⟩
  | @seqNext s first middle second r post left right one two ihOne ihTwo =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context (by simp) rel localised.1 checked.1 control.1 codeOk
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run t context one.sound (by simp) rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨w2, work2, bound2⟩ :=
      ihTwo t1 context result ⟨state1, code1, exceptions1, locals1⟩ localised.2 checked.2
        control.2 (by rw [run_code_sharp one]; exact codeOk)
    refine ⟨w1 + w2, by simp only [compileProgExactHOLW]; exact CrepWorkS.seqNext work1 run1 work2, ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at bound1 bound2 ⊢
    omega
  | @seqStop s first second r post left terminal one ihOne =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context result rel localised.1 checked.1 control.1 codeOk
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run t context one.sound result rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨r0, rfl⟩ := Option.ne_none_iff_exists'.mp terminal
    obtain ⟨c1, rfl⟩ := Option.ne_none_iff_exists'.mp (resultRel_some_ne_none rel1)
    exact ⟨w1, by simp only [compileProgExactHOLW]; exact CrepWorkS.seqStop work1 run1, bound1⟩
  | @iteYes s condition yes no value guardEvents r post bodyEvents guard nonzero body ihBody =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := guard_paid_sharp guard rel checked.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.1.2 checked.1.2 control.1 codeOk
    rw [compile_ite_eq_sharp context compiled]
    refine ⟨2 + loopNodePrice ce + wb, CrepWorkS.iteBranch guardValue ?_, ?_⟩
    · rw [if_pos nonzero]; exact workBody
    · simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
      omega
  | @iteNo s condition yes no guardEvents r post bodyEvents guard body ihBody =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := guard_paid_sharp guard rel checked.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.2 checked.2 control.2 codeOk
    rw [compile_ite_eq_sharp context compiled]
    refine ⟨2 + loopNodePrice ce + wb, CrepWorkS.iteBranch guardValue ?_, ?_⟩
    · simpa using workBody
    · simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
      omega
  | @whileFalse s condition body guardEvents guard =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    rw [compile_while_eq_sharp context compiled]
    refine ⟨2 + 2 + loopNodePrice ce, CrepWorkS.whileExit ?_, ?_⟩
    · intro word hw
      rw [guardValue] at hw
      simp only [Option.some.injEq, HolWordLab.word.injEq] at hw
      exact hw.symm
    · simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound ⊢
      omega
  | @whileTimeout s condition body value guardEvents guard nonzero clock =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    have targetClock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    rw [compile_while_eq_sharp context compiled]
    refine ⟨2 + 2 + loopNodePrice ce, CrepWorkS.whileTimeout guardValue nonzero targetClock, ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound ⊢
    omega
  | @whileNext s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control codeOk
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole (by rw [run_code_sharp one]; exact codeOk)
    rw [compile_while_eq_sharp context compiled] at workRest ⊢
    refine ⟨2 + 2 + loopNodePrice ce + wb + wr,
      CrepWorkS.whileLoop guardValue nonzero targetClock workBody run1 (Or.inl rfl) workRest, ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody boundRest ⊢
    omega
  | @whileContinue s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control codeOk
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole (by rw [run_code_sharp one]; exact codeOk)
    rw [compile_while_eq_sharp context compiled] at workRest ⊢
    refine ⟨2 + 2 + loopNodePrice ce + wb + wr,
      CrepWorkS.whileLoop guardValue nonzero targetClock workBody run1 (Or.inr rfl) workRest, ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody boundRest ⊢
    omega
  | @whileBreak s condition body value guardEvents post bodyEvents guard nonzero clock one
      ihOne =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control codeOk
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, _⟩ := rel1
    rw [compile_while_eq_sharp context compiled]
    refine ⟨2 + 2 + loopNodePrice ce + wb,
      CrepWorkS.whileStop guardValue nonzero targetClock workBody run1 (by simp), ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
    omega
  | @whilePropagate s condition body value guardEvents post bodyEvents bodyResult guard nonzero
      clock notBreak notContinue one ihOne =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid_sharp guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context result relBody localised.2 checked.2 control codeOk
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound result relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    rw [compile_while_eq_sharp context compiled]
    refine ⟨2 + 2 + loopNodePrice ce + wb,
      CrepWorkS.whileStop guardValue nonzero targetClock workBody run1
        ⟨resultRel_some_ne_none rel1, resultRel_not_continue notContinue rel1⟩, ?_⟩
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at guardBound boundBody ⊢
    omega
  | @assignValue s kind name expression value events expr valid =>
    intro t context result rel localised checked control codeOk
    cases kind with
    | «global» => simp [localisedProgHOL] at localised
    | «local» =>
      simp only [localisedProgHOL, sharpSitesProg] at localised checked
      have paid := expression_paid_sharp expr rel checked
      have length := compiled_length_sharp expr.sound rel localised
      simp only [compileProgExactHOLW]
      refine sharp_bounded_paid_sharp (sharp_bounded_local_assign context name expression) ?_
      rw [length]
      simp only [globalEvents]
      simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
      try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
      omega
  | @storeValue s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid_sharp dst rel checked.1
    have paidValue := expression_paid_sharp src rel checked.2
    have length := compiled_length_sharp src.sound rel localised.2
    simp only [compileProgExactHOLW]
    refine sharp_bounded_paid_sharp (sharp_bounded_store_compiled context destination source) ?_
    rw [length]
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    omega
  | @store32Value s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid_sharp dst rel checked.1
    have paidValue := expression_paid_sharp src rel checked.2
    simp only [compileProgExactHOLW]
    refine sharp_bounded_paid_sharp (sharp_bounded_store32_compiled context destination source) ?_
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    omega
  | @storeByteValue s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid_sharp dst rel checked.1
    have paidValue := expression_paid_sharp src rel checked.2
    simp only [compileProgExactHOLW]
    refine sharp_bounded_paid_sharp (sharp_bounded_storeByte_compiled context destination source) ?_
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paidAddress paidValue ⊢
    omega
  | @returnValue s expression value events expr size =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg] at localised checked
    have paid := expression_paid_sharp expr rel checked
    have length := compiled_length_sharp expr.sound rel localised
    simp only [compileProgExactHOLW]
    refine sharp_bounded_paid_sharp (sharp_bounded_return_compiled context expression) ?_
    rw [length]
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
    omega
  | @raiseValue s exceptionId expression value events shape expr declared shapeMatches size =>
    intro t context result rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg] at localised checked
    have paid := expression_paid_sharp expr rel checked
    have length := compiled_length_sharp expr.sound rel localised
    simp only [compileProgExactHOLW]
    refine sharp_bounded_paid_sharp (sharp_bounded_raise_compiled context exceptionId expression) ?_
    rw [length]
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_nil] at paid ⊢
    omega
  | @declareValue s name shape initializer body value initEvents bodyEvents result post init
      shapeMatch bodyRun ihBody =>
    intro t context resultOk rel localised checked control codeOk
    simp only [localisedProgHOL, sharpSitesProg, sourceControlProg_sharp, Bool.and_eq_true]
      at localised checked control
    have paid := expression_paid_sharp init rel checked.1
    obtain ⟨bodyContext, bodyState, bodyFuncs, bodyRel, lift⟩ :=
      dec_transfer_sharp init.sound shapeMatch rel localised.1
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody bodyState bodyContext resultOk bodyRel localised.2 checked.2 control codeOk
    refine ⟨_, lift wb workBody, ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil]
    try simp only [sharpScore_statement, sharpScore_append, sharpScore_copy, sharpScore_frame, sharpScore_scalar, sharpScore_memory, sharpScore_expression, sharpScore_nil] at paid boundBody ⊢
    omega
  | @callDone s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents result post args lookup clock bodyRun plan ihBody =>
    intro t context resultOk rel localised checked control codeOk
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have bodyOk := call_body_ok_sharp plan resultOk
    have checkedArgs : sharpSitesList sharpReplayBound arguments = true := by
      rcases info with _ | ⟨dest, _ | ⟨a, b, c⟩⟩ <;> simp_all [sharpSitesProg]
    rw [callGlobalEvents_localised localised, List.append_nil]
    exact call_done_transfer_sharp args lookup clock bodyRun plan resultOk rel localised checkedArgs
      (fun t' c' rel' loc' =>
        ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk)
  | @callTimeout s info function arguments values body callee returnShape args lookup clock =>
    intro t context resultOk rel localised checked control codeOk
    have checkedArgs : sharpSitesList sharpReplayBound arguments = true := by
      rcases info with _ | ⟨dest, _ | ⟨a, b, c⟩⟩ <;> simp_all [sharpSitesProg]
    rw [callGlobalEvents_localised localised, List.append_nil]
    exact call_timeout_transfer_sharp args lookup clock rel localised checkedArgs
  | @callHandler s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents handlerEntry handlerProgram handlerEvents result post args lookup clock bodyRun
      plan handlerRun ihBody ihHandler =>
    intro t context resultOk rel localised checked control codeOk
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
    exact call_handler_transfer_sharp args lookup clock bodyRun plan rel localised checked.1
      (fun t' c' rel' loc' =>
        ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk)
      (fun t' c' rel' loc' =>
        ihHandler t' c' resultOk rel' loc' checked.2 control handlerCode)
  | @declareCallReturn s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents continuationEvents result post args lookup clock bodyRun shapeMatch
      continuationRun ihBody ihContinuation =>
    intro t context resultOk rel localised checked control codeOk
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
    exact decCall_return_transfer_sharp args lookup clock bodyRun shapeMatch rel localised checked.1
      (fun t' c' rel' loc' => ihBody t' c' (by simp) rel' loc' bodyStatic.1 bodyStatic.2 codeOk)
      (fun t' c' rel' => ihContinuation t' c' resultOk rel' localisedCont checked.2 control
        contCode)
  | @declareCallTimeout s name shape function arguments continuation values body callee
      returnShape args lookup clock =>
    intro t context resultOk rel localised checked control codeOk
    simp only [sharpSitesProg, Bool.and_eq_true] at checked
    exact decCall_timeout_transfer_sharp args lookup clock rel localised checked.1
  | @declareCallStopped s name shape function arguments continuation values body callee
      returnShape bodyResult bodyPost bodyEvents args lookup clock bodyRun terminal ihBody =>
    intro t context resultOk rel localised checked control codeOk
    simp only [sharpSitesProg, Bool.and_eq_true] at checked
    obtain ⟨vshapes, hsrc, _, _, _⟩ :=
      lookupCodeHOLFinite_some_inv s.code.lookup function values body callee returnShape lookup
    have bodyStatic := codeOk function vshapes body returnShape hsrc
    have stop := decCall_stop_cases_sharp terminal resultOk
    have bodyOk : bodyResult ≠ some .error := by
      rcases stop with h | ⟨f, h⟩ | ⟨eid, v, h⟩ <;> rw [h] <;> simp
    exact decCall_stopped_transfer_sharp args lookup clock bodyRun stop rel localised checked.1
      (fun t' c' rel' loc' => ihBody t' c' bodyOk rel' loc' bodyStatic.1 bodyStatic.2 codeOk)
  | @primitiveValue s name operator arguments values value args operation valid =>
    intro t context resultOk rel localised checked control codeOk
    simp only [sharpSitesProg] at checked
    exact primitive_transfer_sharp args operation valid rel localised checked
  | @external s function configuration configurationLength array arrayLength result post run =>
    intro t context resultOk rel localised checked control codeOk
    exact external_transfer_sharp run resultOk rel localised checked
  | @sharedLoad s operator kind name address result post run =>
    intro t context resultOk rel localised checked control codeOk
    exact shared_load_transfer_sharp run resultOk rel localised checked
  | @sharedStore s operator address value result post run =>
    intro t context resultOk rel localised checked control codeOk
    exact shared_store_transfer_sharp run resultOk rel localised checked
  | _ =>
    intro t context result rel localised checked control codeOk
    first
      | exact absurd rfl result
      | (simp [sourceControlProg_sharp] at control)

#print axioms source_control_crep_work_sharp
end InitECandidate.Runtime.FineCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every localised source program is in the transferred fragment; the only
excluded constructor (global assignment) is never localised. -/
theorem covered_of_localised_sharp : ∀ p : ProgHOL 64, localisedProgHOL p = true →
    sourceControlProg_sharp p = true
  | .skip, _ | .break, _ | .continue, _ | .tick, _ | .annot _ _, _ => by simp [sourceControlProg_sharp]
  | .assign .local _ _, _ => by simp [sourceControlProg_sharp]
  | .assign .global _ _, h => by simp [localisedProgHOL] at h
  | .store _ _, _ | .store32 _ _, _ | .storeByte _ _, _ | .return _, _ | .raise _ _, _ => by
    simp [sourceControlProg_sharp]
  | .primitive _ _ _, _ | .extCall _ _ _ _ _, _ | .shMemLoad _ _ _ _, _
  | .shMemStore _ _ _, _ => by simp [sourceControlProg_sharp]
  | .seq a b, h => by
    simp only [localisedProgHOL, Bool.and_eq_true] at h
    simp [sourceControlProg_sharp, covered_of_localised_sharp a h.1, covered_of_localised_sharp b h.2]
  | .ite _ a b, h => by
    simp only [localisedProgHOL, Bool.and_eq_true] at h
    simp [sourceControlProg_sharp, covered_of_localised_sharp a h.1.2, covered_of_localised_sharp b h.2]
  | .while _ b, h => by
    simp only [localisedProgHOL, Bool.and_eq_true] at h
    simp [sourceControlProg_sharp, covered_of_localised_sharp b h.2]
  | .dec _ _ _ b, h => by
    simp only [localisedProgHOL, Bool.and_eq_true] at h
    simp [sourceControlProg_sharp, covered_of_localised_sharp b h.2]
  | .decCall _ _ _ _ b, h => by
    simp only [localisedProgHOL, Bool.and_eq_true] at h
    simp [sourceControlProg_sharp, covered_of_localised_sharp b h.2]
  | .call none _ _, _ | .call (some (_, none)) _ _, _ => by simp [sourceControlProg_sharp]
  | .call (some (dest, some (eid, var, handler))) f args, h => by
    have hh : localisedProgHOL handler = true := by
      rcases dest with _ | ⟨k, n⟩ <;> (try rcases k) <;> simp_all [localisedProgHOL]
    simp [sourceControlProg_sharp, covered_of_localised_sharp handler hh]
termination_by p => sizeOf p

/-- Executed source-to-Crep work transfer for every exact source trace.
Premises: the exact source trace and a non-error result, the four original
`pc_compile_correct` relations, `localised_prog`, and the static guest
load-site certificate on the program and every function body. The compiled
Crep program's actual execution has a work derivation paid by the source
event vector under `sourceCrepWeights`. -/
theorem source_crep_executed_work_sharp {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) (t : CrepSemHOLState 64 F)
    (context : PanToCrepContextExact 64) (resultOk : r ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → sharpSitesProg sharpReplayBound body = true) :
    CrepWorkPaid_sharp t (compileProgExactHOLW context p) events := by
  apply source_control_crep_work_sharp run t context resultOk rel localised checked
    (covered_of_localised_sharp p localised)
  intro function shapes body returnShape lookup
  obtain ⟨bodyLocalised, _, _⟩ := codeRelExactHOLW_imp context s.code t.code rel.code function
    shapes body returnShape lookup
  exact ⟨codeChecked function shapes body returnShape lookup,
    covered_of_localised_sharp body bodyLocalised⟩

/-- Selected-trace form: the canonical source execution cost pays for the
compiled Crep execution. -/
theorem source_execution_cost_pays_crep_sharp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64)
    (resultOk : (evaluateHOLFiniteState s p).1 ≠ some .error)
    (rel : SourceCrepRel context s t) (localised : localisedProgHOL p = true)
    (checked : sharpSitesProg sharpReplayBound p = true)
    (codeChecked : ∀ function shapes body returnShape,
      s.code.lookup function = some (shapes, body, returnShape) → sharpSitesProg sharpReplayBound body = true) :
    ∃ w, CrepWorkS t (compileProgExactHOLW context p) w ∧
      w ≤ sharpScore (sourceExecutionEvents s p) :=
  source_crep_executed_work_sharp (sourceExecutionEvents_run s p) t context resultOk rel localised
    checked codeChecked

#print axioms covered_of_localised_sharp
#print axioms source_crep_executed_work_sharp
#print axioms source_execution_cost_pays_crep_sharp
end InitECandidate.Runtime.FineCost
