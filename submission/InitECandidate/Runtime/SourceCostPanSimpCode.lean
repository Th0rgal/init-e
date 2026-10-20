import InitECandidate.Runtime.SourceCostPanSimpCodeBase
import InitECandidate.Runtime.SourceCostPanSimpAssoc
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! `pan_simp` on the installed code map: a non-error source run under the
original code map is matched, with no more work, by a run under the code map
whose bodies are `pan_simp`-compiled. Callee bodies are transported
recursively and then compiled with `seq_assoc` and `ret_to_tail`. -/

theorem simpCode_callGlobal {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (info) :
    callGlobalEvents { s with code := c } info = callGlobalEvents s info := rfl

theorem simpCode_preserved {F : Type} {s post : PanSemStateFiniteExact 64 F} {p r ev}
    (run : StatementRun s p r post ev) (ok : r ≠ some .error)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hc : PanSimp.CodeRel s.code c) : post.code = s.code :=
  (PanSimp.codeSimAll p s r post c run.sound ok hc).2

theorem simpCode_plan_error {F : Type} (s bodyPost : PanSemStateFiniteExact 64 F) info returnShape :
    callCostPlan s info returnShape (some .error) bodyPost =
      .done (some .error) (emptyLocalsHOLFinite bodyPost) := by
  unfold callCostPlan; rfl

theorem simpCode_plan_handler_code {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    entry.code = bodyPost.code := by
  unfold callCostPlan at h
  repeat' split at h
  all_goals (cases h)
  all_goals rfl

theorem simpCode_stopPlan {F : Type} (bodyResult : Option (PanSemResultExact 64))
    (bodyPost : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    declareCallStopPlan bodyResult { bodyPost with code := c } =
      ((declareCallStopPlan bodyResult bodyPost).1,
        { (declareCallStopPlan bodyResult bodyPost).2 with code := c }) := by
  unfold declareCallStopPlan
  split <;> rfl

/-- A non-error callee body run under the original code becomes a run of the
compiled body under the compiled code map. -/
theorem simpCode_body {F : Type} {s post : PanSemStateFiniteExact 64 F} {body : ProgHOL 64} {r ev ev1}
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (ok : r ≠ some .error)
    (moved : StatementRun { s with code := c } body r { post with code := c } ev1)
    (le : SimpWorkLe ev1 ev) :
    ∃ ev', StatementRun { s with code := c } (panSimpCompileHOL body) r { post with code := c } ev' ∧
      SimpWorkLe ev' ev := by
  obtain ⟨e1, r1, l1⟩ := simp_seqAssoc_run (F := F) body .skip moved
  obtain ⟨e2, r2, l2⟩ := simp_retToTail_run (F := F) _ r1 ok
  exact ⟨e2, r2, l2.trans (l1.trans le)⟩

theorem simp_code_run {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64} {r post ev}
    (run : StatementRun s p r post ev) :
    r ≠ some .error → ∀ (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
      PanSimp.CodeRel s.code c →
      ∃ ev', StatementRun { s with code := c } p r { post with code := c } ev' ∧ SimpWorkLe ev' ev := by
  induction run with
  | assignInvalid expr invalid => intro ok; exact absurd rfl ok
  | assignFailure expr => intro ok; exact absurd rfl ok
  | returnOversize expr size => intro ok; exact absurd rfl ok
  | returnFailure expr => intro ok; exact absurd rfl ok
  | raiseFailure expr => intro ok; exact absurd rfl ok
  | storeRejected dst src write => intro ok; exact absurd rfl ok
  | storeSourceFailure dst src => intro ok; exact absurd rfl ok
  | storeAddressFailure dst => intro ok; exact absurd rfl ok
  | store32Rejected dst src write => intro ok; exact absurd rfl ok
  | storeByteRejected dst src write => intro ok; exact absurd rfl ok
  | declareMismatch init mismatch => intro ok; exact absurd rfl ok
  | declareFailure init => intro ok; exact absurd rfl ok
  | callArgumentsFailure args => intro ok; exact absurd rfl ok
  | callLookupFailure args lookup => intro ok; exact absurd rfl ok
  | declareCallArgumentsFailure args => intro ok; exact absurd rfl ok
  | declareCallLookupFailure args lookup => intro ok; exact absurd rfl ok
  | declareCallRejectedReturn args lookup clock bodyRun shapeMismatch => intro ok; exact absurd rfl ok
  | iteInvalidGuard guard invalid => intro ok; exact absurd rfl ok
  | whileInvalidGuard guard invalid => intro ok; exact absurd rfl ok
  | whileMissingGuard guard => intro ok; exact absurd rfl ok
  | storeInvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | store32InvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | storeByteInvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | store32InvalidValue dst src invalid => intro ok; exact absurd rfl ok
  | storeByteInvalidValue dst src invalid => intro ok; exact absurd rfl ok
  | primitiveInvalid args operation valid => intro ok; exact absurd rfl ok
  | primitiveRejected args operation => intro ok; exact absurd rfl ok
  | primitiveArgumentsFailure args => intro ok; exact absurd rfl ok
  | raiseUndeclared expr missing => intro ok; exact absurd rfl ok
  | raiseRejectedValue expr declared invalid => intro ok; exact absurd rfl ok
  | skip s => intro _ c _; exact ⟨_, .skip _, SimpWorkLe.refl _⟩
  | breakStmt s => intro _ c _; exact ⟨_, .breakStmt _, SimpWorkLe.refl _⟩
  | continueStmt s => intro _ c _; exact ⟨_, .continueStmt _, SimpWorkLe.refl _⟩
  | annotation => intro _ c _; exact ⟨_, .annotation, SimpWorkLe.refl _⟩
  | tickStep clock => intro _ c _; exact ⟨_, .tickStep clock, SimpWorkLe.refl _⟩
  | tickTimeout clock => intro _ c _; exact ⟨_, .tickTimeout clock, SimpWorkLe.refl _⟩
  | seqNext one two ihOne ihTwo =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne (by simp) c hc
    obtain ⟨e2, r2, l2⟩ := ihTwo ok c (by rw [simpCode_preserved one (by simp) c hc]; exact hc)
    exact ⟨_, .seqNext r1 r2, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | seqStop terminal one ihOne =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne ok c hc
    exact ⟨_, .seqStop terminal r1, l1⟩
  | iteYes guard nonzero body ihBody =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihBody ok c hc
    exact ⟨_, .iteYes (simpCode_costed c guard) nonzero r1, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | iteNo guard body ihBody =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihBody ok c hc
    exact ⟨_, .iteNo (simpCode_costed c guard) r1, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | whileFalse guard => intro _ c _; exact ⟨_, .whileFalse (simpCode_costed c guard), SimpWorkLe.refl _⟩
  | whileTimeout guard nonzero clock =>
    intro _ c _; exact ⟨_, .whileTimeout (simpCode_costed c guard) nonzero clock, SimpWorkLe.refl _⟩
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne (by simp) c hc
    obtain ⟨e2, r2, l2⟩ := ihRest ok c (by rw [simpCode_preserved one (by simp) c hc]; exact hc)
    exact ⟨_, .whileNext (simpCode_costed c guard) nonzero clock r1 r2, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne (by simp) c hc
    obtain ⟨e2, r2, l2⟩ := ihRest ok c (by rw [simpCode_preserved one (by simp) c hc]; exact hc)
    exact ⟨_, .whileContinue (simpCode_costed c guard) nonzero clock r1 r2, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | whileBreak guard nonzero clock one ihOne =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne (by simp) c hc
    exact ⟨_, .whileBreak (simpCode_costed c guard) nonzero clock r1, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ihOne ok c hc
    exact ⟨_, .whilePropagate (simpCode_costed c guard) nonzero clock notBreak notContinue r1,
      fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | @assignValue s kind name expression value events expr valid =>
    intro _ c _
    have run' := StatementRun.assignValue (simpCode_costed c expr) (s := { s with code := c })
      (kind := kind) (name := name) valid
    rw [simpCode_setKvar] at run'
    exact ⟨_, run', SimpWorkLe.refl _⟩
  | returnValue expr size => intro _ c _; exact ⟨_, .returnValue (simpCode_costed c expr) size, SimpWorkLe.refl _⟩
  | raiseValue expr declared shapeMatches size =>
    intro _ c _
    exact ⟨_, .raiseValue (simpCode_costed c expr) declared shapeMatches size, SimpWorkLe.refl _⟩
  | storeValue dst src write =>
    intro _ c _
    exact ⟨_, .storeValue (simpCode_costed c dst) (simpCode_costed c src) write, SimpWorkLe.refl _⟩
  | store32Value dst src write =>
    intro _ c _
    exact ⟨_, .store32Value (simpCode_costed c dst) (simpCode_costed c src) write, SimpWorkLe.refl _⟩
  | storeByteValue dst src write =>
    intro _ c _
    exact ⟨_, .storeByteValue (simpCode_costed c dst) (simpCode_costed c src) write, SimpWorkLe.refl _⟩
  | declareValue init shapeMatch bodyRun ih =>
    intro ok c hc
    obtain ⟨e1, r1, l1⟩ := ih ok c hc
    exact ⟨_, .declareValue (simpCode_costed c init) shapeMatch r1, fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | @primitiveValue s name operator arguments values value args operation valid =>
    intro _ c _
    refine ⟨_, .primitiveValue ((PanSimp.evalListCodeUpd c s arguments).trans args) operation valid,
      fun co => ?_⟩
    simp only [simpCode_listEvents]
    exact Nat.le_refl _
  | @external s function configuration configurationLength array arrayLength result post run =>
    intro _ c _
    refine ⟨_, .external (evaluateCodeUpd_ExtCall c s function configuration configurationLength
      array arrayLength result post run), ?_⟩
    rw [simpCode_external]; exact SimpWorkLe.refl _
  | @sharedLoad s operator kind name address result post run =>
    intro _ c _
    refine ⟨_, .sharedLoad (evaluateCodeUpd_ShMemLoad c s operator kind name address result post run), ?_⟩
    rw [simpCode_sharedLoad]; exact SimpWorkLe.refl _
  | @sharedStore s operator address value result post run =>
    intro _ c _
    refine ⟨_, .sharedStore (evaluateCodeUpd_ShMemStore c s operator address value result post run), ?_⟩
    rw [simpCode_sharedStore]; exact SimpWorkLe.refl _
  | @callDone s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents result post args lookup clock bodyRun plan ihBody =>
    intro ok c hc
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; rw [simpCode_plan_error] at plan; cases plan; exact ok rfl
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    obtain ⟨e0, r0, l0⟩ := ihBody bodyOk c hc
    obtain ⟨e1, r1, l1⟩ := simpCode_body c bodyOk r0 l0
    exact ⟨_, .callDone args' lookup' clock r1 (simpCode_plan_done c plan), fun co => by
      try have := l1 co
      try have := l2 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩
  | @callHandler s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents handlerEntry handlerProgram handlerEvents result post args lookup clock bodyRun plan
      handlerRun ihBody ihHandler =>
    intro ok c hc
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; rw [simpCode_plan_error] at plan; cases plan
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    obtain ⟨e0, r0, l0⟩ := ihBody bodyOk c hc
    obtain ⟨e1, r1, l1⟩ := simpCode_body c bodyOk r0 l0
    have entryCode : handlerEntry.code = s.code := by
      rw [simpCode_plan_handler_code plan, simpCode_preserved bodyRun bodyOk c hc]; rfl
    obtain ⟨e2, r2, l2⟩ := ihHandler ok c (by rw [entryCode]; exact hc)
    exact ⟨_, .callHandler args' lookup' clock r1 (simpCode_plan_handler c plan) r2,
      fun co => by
        have := l1 co; have := l2 co
        simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
        omega⟩
  | @callTimeout s info function arguments values body callee returnShape args lookup clock =>
    intro _ c hc
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    refine ⟨_, .callTimeout args' lookup' clock, ?_⟩
    simp only [simpCode_listEvents, simpCode_callGlobal]; exact SimpWorkLe.refl _
  | @declareCallTimeout s name shape function arguments continuation values body callee returnShape
      args lookup clock =>
    intro _ c hc
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    refine ⟨_, .declareCallTimeout args' lookup' clock, ?_⟩
    simp only [simpCode_listEvents]; exact SimpWorkLe.refl _
  | @declareCallReturn s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents continuationEvents result post args lookup clock bodyRun shapeMatch
      continuationRun ihBody ihContinuation =>
    intro ok c hc
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    obtain ⟨e0, r0, l0⟩ := ihBody (by simp) c hc
    obtain ⟨e1, r1, l1⟩ := simpCode_body c (by simp) r0 l0
    obtain ⟨e2, r2, l2⟩ := ihContinuation ok c
      (by show PanSimp.CodeRel bodyPost.code c; rw [simpCode_preserved bodyRun (by simp) c hc]; exact hc)
    exact ⟨_, .declareCallReturn args' lookup' clock r1 shapeMatch r2,
      fun co => by
        have := l1 co; have := l2 co
        simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
        omega⟩
  | @declareCallStopped s name shape function arguments continuation values body callee returnShape
      bodyResult bodyPost bodyEvents args lookup clock bodyRun terminal ihBody =>
    intro ok c hc
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; exact ok rfl
    have args' := (PanSimp.evalListCodeUpd c s arguments).trans args
    have lookup' : lookupCodeHOLFinite c.lookup function values =
        some (panSimpCompileHOL body, callee, returnShape) := by
      rw [PanSimp.lookupCodeRel s.code c hc function values, lookup]; rfl
    obtain ⟨e0, r0, l0⟩ := ihBody bodyOk c hc
    obtain ⟨e1, r1, l1⟩ := simpCode_body c bodyOk r0 l0
    have run' := StatementRun.declareCallStopped (name := name) (shape := shape)
      (continuation := continuation) args' lookup' clock r1 terminal
    rw [simpCode_stopPlan] at run'
    exact ⟨_, run', fun co => by
      have := l1 co
      simp only [simpCode_listEvents, simpCode_callGlobal, eventSum_cons, eventSum_append] at *
      omega⟩

/-- Whole `pan_simp` transfer for one statement and its installed code map:
a non-error source run of `p` is matched by a run of `pan_simp$compile p`
under the compiled code map with no more work under every coefficient vector. -/
theorem simp_compile_run {F : Type} {s post : PanSemStateFiniteExact 64 F} {p : ProgHOL 64} {r ev}
    (run : StatementRun s p r post ev) (ok : r ≠ some .error)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hc : PanSimp.CodeRel s.code c) :
    ∃ ev', StatementRun { s with code := c } (panSimpCompileHOL p) r { post with code := c } ev' ∧
      SimpWorkLe ev' ev := by
  obtain ⟨e0, r0, l0⟩ := simp_code_run run ok c hc
  exact simpCode_body c ok r0 l0

#print axioms simp_code_run
#print axioms simp_compile_run
end InitECandidate.Runtime.FineCost
