import InitECandidate.Runtime.SourceCostCrepDec
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Source statements currently covered by the checked transfer. -/
def sourceControlProg : ProgHOL 64 → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign VarKind.«local» _ _ | .store _ _ | .store32 _ _ | .storeByte _ _ | .return _ | .raise _ _ => true
  | .seq first second => sourceControlProg first && sourceControlProg second
  | .ite _ yes no => sourceControlProg yes && sourceControlProg no
  | .while _ body => sourceControlProg body
  | .dec _ _ _ body => sourceControlProg body
  | _ => false

/-- The transfer conclusion: an executed Crep work derivation for the compiled
program from the related target state, paid by the source trace. -/
def CrepWorkPaid {F : Type} (t : CrepSemHOLState 64 F) (program : CrepProgHOL 64)
    (events : List WorkEvent) : Prop :=
  ∃ w, CrepWork t program w ∧ w ≤ sourceCrepWeights.score (executionWork events)

theorem guard_paid {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {condition : ExpHOL 64} {word : BitVec 64}
    {guardEvents : List WorkEvent} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (guard : CostedExpressionRun s condition (some (.val (.word word))) guardEvents)
    (rel : SourceCrepRel context s t) (checked : bulkLoadSitesExp condition = true)
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    crepNodeWork ce ≤ sourceCrepWeights.score (executionWork guardEvents) := by
  have bound := compiled_expression_crep_work s context t.locals rel.locals condition _
    guard.sound checked
  rw [compiled] at bound
  simp only [crepListWork] at bound
  rw [guard.events_eq]
  unfold expressionCost at bound
  omega

theorem leaf_paid : 1 ≤ sourceCrepWeights.score (executionWork [.statement]) := by
  simp [executionWork, WorkEvent.units, Work.score, Work.plus, sourceCrepWeights]

theorem score_copy (n : Nat) : sourceCrepWeights.score (executionWork [.copy n]) = 8 * n := by
  simp [executionWork, WorkEvent.units, Work.score, Work.plus, sourceCrepWeights]

theorem score_memory (n : Nat) :
    sourceCrepWeights.score (executionWork [.memory n]) = 8 * n := by
  simp [executionWork, WorkEvent.units, Work.score, Work.plus, sourceCrepWeights]

theorem expression_paid {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
    {context : PanToCrepContextExact 64} {expression : ExpHOL 64} {value : ValueHOL 64}
    {events : List WorkEvent}
    (run : CostedExpressionRun s expression (some value) events)
    (rel : SourceCrepRel context s t) (checked : bulkLoadSitesExp expression = true) :
    crepListWork (compileExpExactHOLW context expression).1 ≤
      sourceCrepWeights.score (executionWork events) := by
  have bound := compiled_expression_crep_work s context t.locals rel.locals expression _
    run.sound checked
  rw [run.events_eq]
  exact bound

theorem compiled_length {F : Type} {s : PanSemStateFiniteExact 64 F} {t : CrepSemHOLState 64 F}
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

theorem bounded_paid {F : Type} {t : CrepSemHOLState 64 F} {program : CrepProgHOL 64}
    {bound : Nat} {events : List WorkEvent} (bounded : CrepBounded program bound)
    (le : bound ≤ sourceCrepWeights.score (executionWork events)) :
    CrepWorkPaid t program events := by
  obtain ⟨w, work, bw⟩ := bounded F t
  exact ⟨w, work, by omega⟩

theorem compile_ite_eq (context : PanToCrepContextExact 64) {condition : ExpHOL 64}
    {yes no : ProgHOL 64} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    compileProgExactHOLW context (.ite condition yes no) =
      .ite ce (compileProgExactHOLW context yes) (compileProgExactHOLW context no) := by
  simp only [compileProgExactHOLW, compileIfExactHOLW, compiled]

theorem compile_while_eq (context : PanToCrepContextExact 64) {condition : ExpHOL 64}
    {body : ProgHOL 64} {ce : CrepExpHOL 64} {shape : ShapeHOL}
    (compiled : compileExpExactHOLW context condition = ([ce], shape)) :
    compileProgExactHOLW context (.while condition body) =
      .while ce (compileProgExactHOLW context body) := by
  simp only [compileProgExactHOLW, compileWhileExactHOLW, compiled]

/-- Control-statement transfer: sequential actual successors, selected
conditional branches, every loop guard and iteration, loop exits and timeouts.
Uses the full original Pan-to-Crep premises; the static guest load-site
certificate supplies the expression lowering bound. -/
theorem source_control_crep_work {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun s p r post events) :
    ∀ (t : CrepSemHOLState 64 F) (context : PanToCrepContextExact 64),
      r ≠ some .error → SourceCrepRel context s t → localisedProgHOL p = true →
      bulkLoadSitesProg p = true → sourceControlProg p = true →
      CrepWorkPaid t (compileProgExactHOLW context p) events := by
  induction run with
  | skip s =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.skip t, leaf_paid⟩
  | breakStmt s =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.breakStmt t 0, leaf_paid⟩
  | continueStmt s =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.continueStmt t 0, leaf_paid⟩
  | tickStep clock =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.tick t, leaf_paid⟩
  | tickTimeout clock =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.tick t, leaf_paid⟩
  | annotation =>
    intro t context _ _ _ _ _
    exact ⟨1, by simp only [compileProgExactHOLW]; exact CrepWork.skip t, leaf_paid⟩
  | @seqNext s first middle second r post left right one two ihOne ihTwo =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context (by simp) rel localised.1 checked.1 control.1
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run t context one.sound (by simp) rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨w2, work2, bound2⟩ :=
      ihTwo t1 context result ⟨state1, code1, exceptions1, locals1⟩ localised.2 checked.2
        control.2
    refine ⟨1 + w1 + w2, by simp only [compileProgExactHOLW]; exact CrepWork.seqNext work1 run1 work2, ?_⟩
    rw [score_statement_cons, score_append]
    simp only [sourceCrepWeights] at bound1 bound2 ⊢
    omega
  | @seqStop s first second r post left terminal one ihOne =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨w1, work1, bound1⟩ :=
      ihOne t context result rel localised.1 checked.1 control.1
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run t context one.sound result rel.state rel.code rel.exceptions
        rel.locals localised.1
    obtain ⟨r0, rfl⟩ := Option.ne_none_iff_exists'.mp terminal
    obtain ⟨c1, rfl⟩ := Option.ne_none_iff_exists'.mp (resultRel_some_ne_none rel1)
    refine ⟨1 + w1, by simp only [compileProgExactHOLW]; exact CrepWork.seqStop work1 run1, ?_⟩
    rw [score_statement_cons]
    simp only [sourceCrepWeights] at bound1 ⊢
    omega
  | @iteYes s condition yes no value guardEvents r post bodyEvents guard nonzero body ihBody =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := guard_paid guard rel checked.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.1.2 checked.1.2 control.1
    rw [compile_ite_eq context compiled]
    refine ⟨1 + crepNodeWork ce + wb, CrepWork.iteBranch guardValue ?_, ?_⟩
    · rw [if_pos nonzero]; exact workBody
    · rw [score_statement_cons, score_append]
      simp only [sourceCrepWeights] at guardBound boundBody ⊢
      omega
  | @iteNo s condition yes no guardEvents r post bodyEvents guard body ihBody =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1.1
    have guardBound := guard_paid guard rel checked.1.1 compiled
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody t context result rel localised.2 checked.2 control.2
    rw [compile_ite_eq context compiled]
    refine ⟨1 + crepNodeWork ce + wb, CrepWork.iteBranch guardValue ?_, ?_⟩
    · simpa using workBody
    · rw [score_statement_cons, score_append]
      simp only [sourceCrepWeights] at guardBound boundBody ⊢
      omega
  | @whileFalse s condition body guardEvents guard =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    rw [compile_while_eq context compiled]
    refine ⟨1 + crepNodeWork ce, CrepWork.whileExit ?_, ?_⟩
    · intro word hw
      rw [guardValue] at hw
      simp only [Option.some.injEq, HolWordLab.word.injEq] at hw
      exact hw.symm
    · rw [score_statement_cons]
      simp only [sourceCrepWeights] at guardBound ⊢
      omega
  | @whileTimeout s condition body value guardEvents guard nonzero clock =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    have targetClock : t.clock = 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    rw [compile_while_eq context compiled]
    refine ⟨1 + crepNodeWork ce, CrepWork.whileTimeout guardValue nonzero targetClock, ?_⟩
    rw [score_statement_cons]
    simp only [sourceCrepWeights] at guardBound ⊢
    omega
  | @whileNext s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole
    rw [compile_while_eq context compiled] at workRest ⊢
    refine ⟨1 + crepNodeWork ce + wb + wr,
      CrepWork.whileLoop guardValue nonzero targetClock workBody run1 (Or.inl rfl) workRest, ?_⟩
    rw [score_statement_cons, score_append, score_append]
    simp only [sourceCrepWeights] at guardBound boundBody boundRest ⊢
    omega
  | @whileContinue s condition body value guardEvents middle r post bodyEvents restEvents
      guard nonzero clock one rest ihOne ihRest =>
    intro t context result rel localised checked control
    have localisedWhole := localised
    have checkedWhole := checked
    have controlWhole := control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control
    obtain ⟨r1, t1, run1, state1, code1, exceptions1, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, locals1⟩ := rel1
    obtain ⟨wr, workRest, boundRest⟩ :=
      ihRest t1 context result ⟨state1, code1, exceptions1, locals1⟩ localisedWhole
        checkedWhole controlWhole
    rw [compile_while_eq context compiled] at workRest ⊢
    refine ⟨1 + crepNodeWork ce + wb + wr,
      CrepWork.whileLoop guardValue nonzero targetClock workBody run1 (Or.inr rfl) workRest, ?_⟩
    rw [score_statement_cons, score_append, score_append]
    simp only [sourceCrepWeights] at guardBound boundBody boundRest ⊢
    omega
  | @whileBreak s condition body value guardEvents post bodyEvents guard nonzero clock one
      ihOne =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context (by simp) relBody localised.2 checked.2 control
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound (by simp) relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    obtain ⟨rfl, _⟩ := rel1
    rw [compile_while_eq context compiled]
    refine ⟨1 + crepNodeWork ce + wb,
      CrepWork.whileStop guardValue nonzero targetClock workBody run1 (by simp), ?_⟩
    rw [score_statement_cons, score_append]
    simp only [sourceCrepWeights] at guardBound boundBody ⊢
    omega
  | @whilePropagate s condition body value guardEvents post bodyEvents bodyResult guard nonzero
      clock notBreak notContinue one ihOne =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    obtain ⟨ce, shape, compiled, guardValue⟩ :=
      compiled_guard guard.sound rel.state rel.code rel.locals localised.1
    have guardBound := guard_paid guard rel checked.1 compiled
    have targetClock : t.clock ≠ 0 := by rw [← rel.state.2.2.2.2.2.1]; exact clock
    have relBody : SourceCrepRel context (decClockHOLFinite s) (decClockCrepSemHOL t) :=
      ⟨decClock_state_rel rel.state, rel.code, rel.exceptions, rel.locals⟩
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihOne (decClockCrepSemHOL t) context result relBody localised.2 checked.2 control
    obtain ⟨r1, t1, run1, _, _, _, rel1⟩ :=
      compiled_source_run (decClockCrepSemHOL t) context one.sound result relBody.state
        relBody.code relBody.exceptions relBody.locals localised.2
    rw [compile_while_eq context compiled]
    refine ⟨1 + crepNodeWork ce + wb,
      CrepWork.whileStop guardValue nonzero targetClock workBody run1
        ⟨resultRel_some_ne_none rel1, resultRel_not_continue notContinue rel1⟩, ?_⟩
    rw [score_statement_cons, score_append]
    simp only [sourceCrepWeights] at guardBound boundBody ⊢
    omega
  | @assignValue s kind name expression value events expr valid =>
    intro t context result rel localised checked control
    cases kind with
    | «global» => simp [localisedProgHOL] at localised
    | «local» =>
      simp only [localisedProgHOL, bulkLoadSitesProg] at localised checked
      have paid := expression_paid expr rel checked
      have length := compiled_length expr.sound rel localised
      simp only [compileProgExactHOLW]
      refine bounded_paid (bounded_local_assign context name expression) ?_
      rw [score_statement_cons, score_append, score_copy, length]
      simp only [sourceCrepWeights] at paid ⊢
      omega
  | @storeValue s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid dst rel checked.1
    have paidValue := expression_paid src rel checked.2
    have length := compiled_length src.sound rel localised.2
    simp only [compileProgExactHOLW]
    refine bounded_paid (bounded_store_compiled context destination source) ?_
    rw [score_statement_cons, score_append, score_append, score_memory, length]
    simp only [sourceCrepWeights] at paidAddress paidValue ⊢
    omega
  | @store32Value s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid dst rel checked.1
    have paidValue := expression_paid src rel checked.2
    simp only [compileProgExactHOLW]
    refine bounded_paid (bounded_store32_compiled context destination source) ?_
    rw [score_statement_cons, score_append, score_append, score_memory]
    simp only [sourceCrepWeights] at paidAddress paidValue ⊢
    omega
  | @storeByteValue s destination source address value memory addressEvents valueEvents dst src
      write =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, Bool.and_eq_true] at localised checked
    have paidAddress := expression_paid dst rel checked.1
    have paidValue := expression_paid src rel checked.2
    simp only [compileProgExactHOLW]
    refine bounded_paid (bounded_storeByte_compiled context destination source) ?_
    rw [score_statement_cons, score_append, score_append, score_memory]
    simp only [sourceCrepWeights] at paidAddress paidValue ⊢
    omega
  | @returnValue s expression value events expr size =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg] at localised checked
    have paid := expression_paid expr rel checked
    have length := compiled_length expr.sound rel localised
    simp only [compileProgExactHOLW]
    refine bounded_paid (bounded_return_compiled context expression) ?_
    rw [score_statement_cons, score_append, score_copy, length]
    simp only [sourceCrepWeights] at paid ⊢
    omega
  | @raiseValue s exceptionId expression value events shape expr declared shapeMatches size =>
    intro t context result rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg] at localised checked
    have paid := expression_paid expr rel checked
    have length := compiled_length expr.sound rel localised
    simp only [compileProgExactHOLW]
    refine bounded_paid (bounded_raise_compiled context exceptionId expression) ?_
    rw [score_statement_cons, score_append, score_copy, length]
    simp only [sourceCrepWeights] at paid ⊢
    omega
  | @declareValue s name shape initializer body value initEvents bodyEvents result post init
      shapeMatch bodyRun ihBody =>
    intro t context resultOk rel localised checked control
    simp only [localisedProgHOL, bulkLoadSitesProg, sourceControlProg, Bool.and_eq_true]
      at localised checked control
    have paid := expression_paid init rel checked.1
    obtain ⟨bodyContext, bodyState, bodyRel, lift⟩ :=
      dec_transfer init.sound shapeMatch rel localised.1
    obtain ⟨wb, workBody, boundBody⟩ :=
      ihBody bodyState bodyContext resultOk bodyRel localised.2 checked.2 control
    refine ⟨_, lift wb workBody, ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [score_statement_cons, score_append, executionWork_score_cons, executionWork_score_cons,
      score_append]
    simp only [WorkEvent.units, Work.score, sourceCrepWeights] at paid boundBody ⊢
    omega
  | _ =>
    intro t context result rel localised checked control
    first
      | exact absurd rfl result
      | (simp [sourceControlProg] at control)

#print axioms source_control_crep_work
end InitECandidate.Runtime.FineCost
