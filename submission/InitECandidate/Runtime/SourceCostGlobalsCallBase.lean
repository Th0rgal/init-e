import InitECandidate.Runtime.SourceCostGlobalsRunDec
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Call facts for the `pan_globals` statement transfer: the compiled code map
installs the compiled callee with the same callee locals, and the exit dispatch
of a compiled call matches the source's. -/

theorem globals_lookup_match {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} {b : Bool} (rel : panGlobalsStateRelHOLExact b context s t)
    {function : MlS} {values : List (ValueHOL 64)} {body body' : ProgHOL 64}
    {callee callee' : HolFiniteMapExact MlS (ValueHOL 64)} {returnShape returnShape' : ShapeHOL}
    (src : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (tgt : lookupCodeHOLFinite t.code.lookup function values = some (body', callee', returnShape')) :
    body' = compileProgExactHOL context body ∧ callee' = callee ∧ returnShape' = returnShape := by
  have e1 := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ src
  have e2 := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ tgt
  obtain ⟨vshapes, found, _⟩ := lookupCodeHOLFinite_some_inv _ _ _ _ _ _ src
  have tfound := globalsRel_code rel found
  unfold lookupCodeHOLExact at e1 e2
  rw [found] at e1
  rw [tfound] at e2
  simp only at e1 e2
  split at e1
  · rename_i hc
    rw [if_pos hc] at e2
    simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2
    obtain ⟨_, h2, _⟩ := e1
    obtain ⟨g1, g2, g3⟩ := e2
    exact ⟨g1.symm, holFiniteMapExact_eq_of_lookup_eq (g2.symm.trans h2), g3.symm⟩
  · simp at e1

theorem globals_valid_local {F : Type} {context : PanGlobalsContextExact 64}
    {s t : PanSemStateFiniteExact 64 F} (rel : panGlobalsStateRelHOLExact true context s t)
    (name : MlS) (value : ValueHOL 64) :
    isValidValueHOLExact t.toExact .local name value = isValidValueHOLExact s.toExact .local name value := by
  have same := globalsRel_locals rel
  simp only [isValidValueHOLExact, lookupKvarHOLExact, same]

theorem globals_plan_error {F : Type} (s bodyPost : PanSemStateFiniteExact 64 F) (info) (returnShape) :
    callCostPlan s info returnShape (some .error) bodyPost = .done (some .error) (emptyLocalsHOLFinite bodyPost) := by
  unfold callCostPlan; rfl

theorem globals_body_ok {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult result}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .done result post)
    (ok : result ≠ some .error) : bodyResult ≠ some .error := by
  rintro rfl
  rw [globals_plan_error] at plan
  cases plan
  exact ok rfl

theorem globals_body_ok_handler {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    {info returnShape bodyResult program}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    bodyResult ≠ some .error := by
  rintro rfl
  rw [globals_plan_error] at plan
  cases plan

#print axioms globals_lookup_match
#print axioms globals_valid_local
/-- The call information of a compiled call without a global destination:
only the handler is compiled. -/
def globalsMapInfo (context : PanGlobalsContextExact 64) :
    Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64)) →
    Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64))
  | none => none
  | some (returns, none) => some (returns, none)
  | some (returns, some (exception, handlerVar, handler)) =>
      some (returns, some (exception, handlerVar, compileProgExactHOL context handler))

/-- A source handler dispatch is matched by the compiled call's dispatch into
the compiled handler, from related entry states. -/
theorem globals_plan_handler_match {F : Type} {context : PanGlobalsContextExact 64}
    {s t bodyPost bodyPost' entry : PanSemStateFiniteExact 64 F} {b : Bool}
    (rel : panGlobalsStateRelHOLExact true context s t)
    (relBody : panGlobalsStateRelHOLExact b context bodyPost bodyPost')
    {info returnShape bodyResult program}
    (plan : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    ∃ entry', callCostPlan t (globalsMapInfo context info) returnShape
        bodyResult bodyPost' = .handler entry' (compileProgExactHOL context program) ∧
      panGlobalsStateRelHOLExact true context entry entry' := by
  have eshapes := globalsRel_eshapes rel
  have locals := globalsRel_locals rel
  obtain ⟨dest, exception, handlerVar, rfl⟩ := globals_plan_handler_info plan
  rcases bodyResult with _ | (_ | _ | _ | _ | value | ⟨eid, value⟩ | _)
  all_goals (unfold callCostPlan at plan)
  all_goals (try (simp only at plan; done))
  all_goals (try (simp only at plan; repeat' split at plan) <;> (try cases plan))
  rename_i he _ shape hs hv
  refine ⟨setVarHOLFinite handlerVar value { bodyPost' with locals := t.locals }, ?_, ?_⟩
  · simp only [globalsMapInfo, callCostPlan]
    rw [if_pos he, ← eshapes, hs]
    simp only []
    rw [globals_valid_local rel, if_pos hv]
  · rw [← locals]
    exact globalsRel_setVar (globalsRel_setLocals relBody s.locals) handlerVar value

#print axioms globals_plan_handler_match
theorem globals_plan_handler_back {F : Type} {context : PanGlobalsContextExact 64}
    {s t bodyPost bodyPost' entry' : PanSemStateFiniteExact 64 F}
    (rel : panGlobalsStateRelHOLExact true context s t)
    {info returnShape bodyResult program'}
    (plan' : callCostPlan t (globalsMapInfo context info) returnShape bodyResult bodyPost' =
      .handler entry' program') :
    ∃ entry program, callCostPlan s info returnShape bodyResult bodyPost = .handler entry program := by
  have eshapes := globalsRel_eshapes rel
  obtain ⟨dest, exception, handlerVar, hinfo⟩ := globals_plan_handler_info plan'
  rcases info with _ | ⟨dest0, _ | ⟨exception0, handlerVar0, program0⟩⟩
  · simp [globalsMapInfo] at hinfo
  · simp [globalsMapInfo] at hinfo
  simp only [globalsMapInfo, Option.some.injEq, Prod.mk.injEq] at hinfo
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hinfo
  rcases bodyResult with _ | (_ | _ | _ | _ | value | ⟨eid, value⟩ | _)
  all_goals (unfold callCostPlan at plan')
  all_goals (try (simp only [globalsMapInfo] at plan'; repeat' split at plan') <;> (try cases plan'))
  rename_i he _ shape hs hv
  refine ⟨setVarHOLFinite handlerVar0 value { bodyPost with locals := s.locals }, program0, ?_⟩
  simp only [callCostPlan]
  rw [if_pos he, eshapes, hs]
  simp only []
  rw [← globals_valid_local rel, if_pos hv]

#print axioms globals_plan_handler_back
end InitECandidate.Runtime.FineCost
