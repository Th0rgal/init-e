import InitECandidate.Runtime.SourceCostPanSimpTail
import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Source work never reads the code map: expression values and every
expression, external and shared-memory event list are unchanged when the code
map is replaced. -/

theorem simpCode_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (e : ExpHOL 64) :
    expressionValue { s with code := c } e = expressionValue s e := by
  unfold expressionValue
  exact @evalHOLExact_upd_code_eq 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
    c.lookup

theorem simpCode_events {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (e : ExpHOL 64) :
    expressionEvents { s with code := c } e = expressionEvents s e := by
  refine expressionEvents.induct
    (motive1 := fun e => expressionEvents { s with code := c } e = expressionEvents s e)
    (motive2 := fun fs => expressionFieldEvents { s with code := c } fs = expressionFieldEvents s fs)
    (motive3 := fun es => expressionListEvents { s with code := c } es = expressionListEvents s es)
    ?_ ?_ ?_ ?_ ?_ e
  · intro e ih
    rw [expressionEvents.eq_def, expressionEvents.eq_def]
    cases e <;> simp only at ih <;>
      simp only [resultWords, expressionIsWord, simpCode_value, ih]
    all_goals (first | rfl | congr)
  · simp [expressionFieldEvents]
  · intro name expression tail h1 h2
    simp only [expressionFieldEvents, h1, h2]
  · simp [expressionListEvents]
  · intro head tail h1 h2
    simp only [expressionListEvents, h1, h2]

theorem simpCode_listEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    ∀ es : List (ExpHOL 64), expressionListEvents { s with code := c } es = expressionListEvents s es
  | [] => by simp [expressionListEvents]
  | head :: tail => by
    simp only [expressionListEvents, simpCode_events, simpCode_listEvents s c tail]

theorem simpCode_costed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    {e : ExpHOL 64} {value events} (run : CostedExpressionRun s e value events) :
    CostedExpressionRun { s with code := c } e value events :=
  ⟨by rw [simpCode_value]; exact run.sound, by rw [simpCode_events]; exact run.events_eq⟩

theorem simpCode_external {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    function configuration configurationLength array arrayLength :
    externalEvents { s with code := c } function configuration configurationLength array arrayLength =
      externalEvents s function configuration configurationLength array arrayLength := by
  simp only [externalEvents, externalTransferEvents, simpCode_events, simpCode_value]
  rfl

theorem simpCode_sharedLoad {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) kind name address :
    sharedLoadEvents { s with code := c } kind name address = sharedLoadEvents s kind name address := by
  simp only [sharedLoadEvents, simpCode_events, simpCode_value]
  rfl

theorem simpCode_sharedStore {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) address value :
    sharedStoreEvents { s with code := c } address value = sharedStoreEvents s address value := by
  simp only [sharedStoreEvents, simpCode_events, expressionIsWord, simpCode_value]
  congr

theorem simpCode_valid {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) kind name value :
    isValidValueHOLExact ({ s with code := c } : PanSemStateFiniteExact 64 F).toExact kind name value =
      isValidValueHOLExact s.toExact kind name value := rfl

theorem simpCode_setKvar {F : Type} (kind : VarKind) (name : MlStringHOL) (value : ValueHOL 64)
    (st : PanSemStateFiniteExact 64 F)
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    setKvarHOLFinite kind name value { st with code := c } =
      { setKvarHOLFinite kind name value st with code := c } := by
  cases kind <;> rfl

theorem simpCode_plan_done {F : Type} {s bodyPost post : PanSemStateFiniteExact 64 F}
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    {info returnShape bodyResult result}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    callCostPlan { s with code := c } info returnShape bodyResult { bodyPost with code := c } =
      .done result { post with code := c } := by
  unfold callCostPlan at h
  repeat' split at h
  all_goals (cases h)
  all_goals (unfold callCostPlan; simp_all [simpCode_valid])
  all_goals (first | rfl | (rename_i kind _ _ _; cases kind <;> rfl))

theorem simpCode_plan_handler {F : Type} {s bodyPost entry : PanSemStateFiniteExact 64 F}
    (c : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    {info returnShape bodyResult program}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    callCostPlan { s with code := c } info returnShape bodyResult { bodyPost with code := c } =
      .handler { entry with code := c } program := by
  unfold callCostPlan at h ⊢
  simp only [simpCode_valid]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all
  all_goals (try (split at h <;> simp_all))
  all_goals (try (split at h <;> simp_all))
  all_goals (try (obtain ⟨rfl, rfl⟩ := h; rfl))

#print axioms simpCode_events
#print axioms simpCode_plan_done
#print axioms simpCode_plan_handler
end InitECandidate.Runtime.FineCost
