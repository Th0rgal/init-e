import InitECandidate.Runtime.PanStatementWork
import Flapjack.Pancake.PanSimp
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Shared infrastructure for the `pan_simp` executed-work transfer. -/

/-- Event list `a` costs no more than `b` under every coefficient vector. -/
def SimpWorkLe (a b : List WorkEvent) : Prop :=
  ∀ coeff : Work, coeff.score (executionWork a) ≤ coeff.score (executionWork b)

theorem SimpWorkLe.refl (a : List WorkEvent) : SimpWorkLe a a := fun _ => Nat.le_refl _

theorem SimpWorkLe.trans {a b c : List WorkEvent} (h1 : SimpWorkLe a b) (h2 : SimpWorkLe b c) :
    SimpWorkLe a c := fun coeff => Nat.le_trans (h1 coeff) (h2 coeff)

/-- A run of a program transforms into a run of `q'` with no more work. -/
def SimpRunLe {F : Type} (q q' : ProgHOL 64) : Prop :=
  ∀ {s : PanSemStateFiniteExact 64 F} {r post ev}, StatementRun s q r post ev →
    ∃ ev', StatementRun s q' r post ev' ∧ SimpWorkLe ev' ev

theorem simp_smartSeq_skip (q : ProgHOL 64) : smartSeqHOL (.skip : ProgHOL 64) q = q := rfl

theorem simp_smartSeq_ne {pre : ProgHOL 64} (q : ProgHOL 64) (h : pre ≠ .skip) :
    smartSeqHOL pre q = .seq pre q := by
  cases pre <;> first | exact absurd rfl h | rfl

theorem simp_skip_run {F : Type} {s : PanSemStateFiniteExact 64 F} {r post ev}
    (run : StatementRun s .skip r post ev) : r = none ∧ post = s ∧ ev = [.statement] := by
  cases run; exact ⟨rfl, rfl, rfl⟩

theorem simp_smartSeq_congr {F : Type} {pre q q' : ProgHOL 64} (h : SimpRunLe (F := F) q q') :
    SimpRunLe (F := F) (smartSeqHOL pre q) (smartSeqHOL pre q') := by
  intro s r post ev run
  by_cases hp : pre = .skip
  · subst hp; exact h run
  · rw [simp_smartSeq_ne _ hp] at run ⊢
    cases run with
    | seqNext one two =>
      obtain ⟨e, r2, le⟩ := h two
      refine ⟨_, .seqNext one r2, fun c => ?_⟩
      have := le c
      simp only [executionWork_score_cons, executionWork_score_append] at *
      omega
    | seqStop terminal one => exact ⟨_, .seqStop terminal one, SimpWorkLe.refl _⟩

/-- Loop congruence: a body transformation lifts to every iteration. -/
theorem simp_while_runs {F : Type} {condition : ExpHOL 64} {body body' : ProgHOL 64}
    (hb : SimpRunLe (F := F) body body') :
    SimpRunLe (F := F) (.while condition body) (.while condition body') := by
  intro s r post ev run
  generalize hq : ProgHOL.while condition body = q at run
  induction run with
  | whileFalse guard =>
    cases hq; exact ⟨_, .whileFalse guard, SimpWorkLe.refl _⟩
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    cases hq
    obtain ⟨e1, r1, l1⟩ := hb one
    obtain ⟨e2, r2, l2⟩ := ihRest rfl
    refine ⟨_, .whileNext guard nonzero clock r1 r2, fun c => ?_⟩
    have := l1 c; have := l2 c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    cases hq
    obtain ⟨e1, r1, l1⟩ := hb one
    obtain ⟨e2, r2, l2⟩ := ihRest rfl
    refine ⟨_, .whileContinue guard nonzero clock r1 r2, fun c => ?_⟩
    have := l1 c; have := l2 c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | whileBreak guard nonzero clock one ihOne =>
    cases hq
    obtain ⟨e1, r1, l1⟩ := hb one
    refine ⟨_, .whileBreak guard nonzero clock r1, fun c => ?_⟩
    have := l1 c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | whileTimeout guard nonzero clock =>
    cases hq; exact ⟨_, .whileTimeout guard nonzero clock, SimpWorkLe.refl _⟩
  | whileMissingGuard guard =>
    cases hq; exact ⟨_, .whileMissingGuard guard, SimpWorkLe.refl _⟩
  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    cases hq
    obtain ⟨e1, r1, l1⟩ := hb one
    refine ⟨_, .whilePropagate guard nonzero clock notBreak notContinue r1, fun c => ?_⟩
    have := l1 c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | whileInvalidGuard guard invalid =>
    cases hq; exact ⟨_, .whileInvalidGuard guard invalid, SimpWorkLe.refl _⟩
  | _ => cases hq

/-- The handler-body map used by `seq_assoc` and `ret_to_tail` on call
information. -/
def simpMapInfo (g : ProgHOL 64 → ProgHOL 64) :
    Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64)) →
    Option (Option (VarKind × MlStringHOL) × Option (MlStringHOL × MlStringHOL × ProgHOL 64))
  | none => none
  | some (returns, none) => some (returns, none)
  | some (returns, some (exception, handlerVar, handler)) =>
      some (returns, some (exception, handlerVar, g handler))

theorem simp_plan_map_done {F : Type} (g : ProgHOL 64 → ProgHOL 64)
    {s : PanSemStateFiniteExact 64 F} {info returnShape bodyResult}
    {bodyPost post : PanSemStateFiniteExact 64 F} {result : Option (PanSemResultExact 64)}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .done result post) :
    callCostPlan s (simpMapInfo g info) returnShape bodyResult bodyPost = .done result post := by
  rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
  · exact h
  · exact h
  · simp only [simpMapInfo]
    unfold callCostPlan at h ⊢
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all
    all_goals (try (split at h <;> simp_all))

theorem simp_plan_map_handler {F : Type} (g : ProgHOL 64 → ProgHOL 64)
    {s : PanSemStateFiniteExact 64 F} {info returnShape bodyResult}
    {bodyPost entry : PanSemStateFiniteExact 64 F} {program : ProgHOL 64}
    (h : callCostPlan s info returnShape bodyResult bodyPost = .handler entry program) :
    callCostPlan s (simpMapInfo g info) returnShape bodyResult bodyPost = .handler entry (g program) ∧
      ∃ returns exception handlerVar, info = some (returns, some (exception, handlerVar, program)) := by
  rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
  · unfold callCostPlan at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all
    all_goals (try (split at h <;> simp_all))
  · unfold callCostPlan at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all
    all_goals (try (split at h <;> simp_all))
  · simp only [simpMapInfo]
    unfold callCostPlan at h ⊢
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all
    all_goals (try (split at h <;> simp_all))

theorem simp_call_runs {F : Type} (g : ProgHOL 64 → ProgHOL 64) {info function arguments}
    (hh : ∀ returns exception handlerVar handler,
      info = some (returns, some (exception, handlerVar, handler)) →
      SimpRunLe (F := F) handler (g handler)) :
    SimpRunLe (F := F) (.call info function arguments)
      (.call (simpMapInfo g info) function arguments) := by
  intro s r post ev run
  cases run with
  | callDone args lookup clock bodyRun plan =>
    exact ⟨_, .callDone args lookup clock bodyRun (simp_plan_map_done g plan), SimpWorkLe.refl _⟩
  | callHandler args lookup clock bodyRun plan handlerRun =>
    obtain ⟨plan', returns, exception, handlerVar, hinfo⟩ := simp_plan_map_handler g plan
    obtain ⟨e, r', le⟩ := hh returns exception handlerVar _ hinfo handlerRun
    refine ⟨_, .callHandler args lookup clock bodyRun plan' r', fun c => ?_⟩
    have := le c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | callArgumentsFailure args => exact ⟨_, .callArgumentsFailure args, SimpWorkLe.refl _⟩
  | callLookupFailure args lookup => exact ⟨_, .callLookupFailure args lookup, SimpWorkLe.refl _⟩
  | callTimeout args lookup clock => exact ⟨_, .callTimeout args lookup clock, SimpWorkLe.refl _⟩

theorem simp_decCall_runs {F : Type} {name shape function arguments} {cont cont' : ProgHOL 64}
    (hc : SimpRunLe (F := F) cont cont') :
    SimpRunLe (F := F) (.decCall name shape function arguments cont)
      (.decCall name shape function arguments cont') := by
  intro s r post ev run
  cases run with
  | declareCallReturn args lookup clock bodyRun shapeMatch continuationRun =>
    obtain ⟨e, r', le⟩ := hc continuationRun
    refine ⟨_, .declareCallReturn args lookup clock bodyRun shapeMatch r', fun c => ?_⟩
    have := le c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | declareCallArgumentsFailure args => exact ⟨_, .declareCallArgumentsFailure args, SimpWorkLe.refl _⟩
  | declareCallLookupFailure args lookup =>
    exact ⟨_, .declareCallLookupFailure args lookup, SimpWorkLe.refl _⟩
  | declareCallTimeout args lookup clock =>
    exact ⟨_, .declareCallTimeout args lookup clock, SimpWorkLe.refl _⟩
  | declareCallRejectedReturn args lookup clock bodyRun mismatch =>
    exact ⟨_, .declareCallRejectedReturn args lookup clock bodyRun mismatch, SimpWorkLe.refl _⟩
  | declareCallStopped args lookup clock bodyRun terminal =>
    exact ⟨_, .declareCallStopped args lookup clock bodyRun terminal, SimpWorkLe.refl _⟩

theorem simp_dec_runs {F : Type} {name shape value} {body body' : ProgHOL 64}
    (hb : SimpRunLe (F := F) body body') :
    SimpRunLe (F := F) (.dec name shape value body) (.dec name shape value body') := by
  intro s r post ev run
  cases run with
  | declareValue init shapeMatch bodyRun =>
    obtain ⟨e, r', le⟩ := hb bodyRun
    refine ⟨_, .declareValue init shapeMatch r', fun c => ?_⟩
    have := le c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | declareMismatch init mismatch => exact ⟨_, .declareMismatch init mismatch, SimpWorkLe.refl _⟩
  | declareFailure init => exact ⟨_, .declareFailure init, SimpWorkLe.refl _⟩

theorem simp_ite_runs {F : Type} {condition} {yes yes' no no' : ProgHOL 64}
    (hy : SimpRunLe (F := F) yes yes') (hn : SimpRunLe (F := F) no no') :
    SimpRunLe (F := F) (.ite condition yes no) (.ite condition yes' no') := by
  intro s r post ev run
  cases run with
  | iteYes guard nonzero body =>
    obtain ⟨e, r', le⟩ := hy body
    refine ⟨_, .iteYes guard nonzero r', fun c => ?_⟩
    have := le c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | iteNo guard body =>
    obtain ⟨e, r', le⟩ := hn body
    refine ⟨_, .iteNo guard r', fun c => ?_⟩
    have := le c
    simp only [executionWork_score_cons, executionWork_score_append] at *
    omega
  | iteInvalidGuard guard invalid => exact ⟨_, .iteInvalidGuard guard invalid, SimpWorkLe.refl _⟩

#print axioms simp_call_runs
#print axioms simp_decCall_runs

#print axioms simp_smartSeq_congr
#print axioms simp_while_runs
#print axioms simp_plan_map_done
#print axioms simp_plan_map_handler
end InitECandidate.Runtime.FineCost
