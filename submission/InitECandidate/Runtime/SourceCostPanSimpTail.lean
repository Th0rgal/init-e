import InitECandidate.Runtime.SourceCostPanSimpBase
import Flapjack.Pancake.Proofs.PanSimp.RetToTailAssembly
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! `pan_simp$ret_to_tail` never increases executed source work on non-error
runs. The tail-call rewrite reuses the original call's argument, lookup,
clock and callee-body premises; its result and final state are forced by the
pinned `evaluateSeqCallRetEqHOL` and `StatementRun.sound`. -/

/-- Non-error run transformation with no more work. -/
def SimpRunLeOk (fn : Flapjack.Pancake.PanLang.MlS) {F : Type} (q q' : ProgHOL 64) : Prop :=
  ∀ {s : PanSemStateFiniteExact 64 F} {r post ev}, StatementRun fn s q r post ev →
    r ≠ some .error → ∃ ev', StatementRun fn s q' r post ev' ∧ SimpWorkLe ev' ev

theorem simpOk_while_runs {F : Type} {condition : ExpHOL 64} {body body' : ProgHOL 64}
    (hb : SimpRunLeOk fn (F := F) body body') :
    SimpRunLeOk fn (F := F) (.while condition body) (.while condition body') := by
  intro s r post ev run ok
  generalize hf : fn = f0 at run
  generalize hq : ProgHOL.while condition body = q at run
  induction run with
  | whileFalse guard =>
    cases hq; subst hf; exact ⟨_, .whileFalse guard, SimpWorkLe.refl _⟩
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    cases hq; subst hf
    obtain ⟨e1, r1, l1⟩ := hb one (by simp)
    obtain ⟨e2, r2, l2⟩ := ihRest ok rfl rfl
    refine ⟨_, .whileNext guard nonzero clock r1 r2, fun c => ?_⟩
    have := l1 c; have := l2 c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    cases hq; subst hf
    obtain ⟨e1, r1, l1⟩ := hb one (by simp)
    obtain ⟨e2, r2, l2⟩ := ihRest ok rfl rfl
    refine ⟨_, .whileContinue guard nonzero clock r1 r2, fun c => ?_⟩
    have := l1 c; have := l2 c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | whileBreak guard nonzero clock one ihOne =>
    cases hq; subst hf
    obtain ⟨e1, r1, l1⟩ := hb one (by simp)
    refine ⟨_, .whileBreak guard nonzero clock r1, fun c => ?_⟩
    have := l1 c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | whileTimeout guard nonzero clock =>
    cases hq; subst hf; exact ⟨_, .whileTimeout guard nonzero clock, SimpWorkLe.refl _⟩
  | whileMissingGuard guard =>
    cases hq; subst hf; exact ⟨_, .whileMissingGuard guard, SimpWorkLe.refl _⟩
  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    cases hq; subst hf
    obtain ⟨e1, r1, l1⟩ := hb one ok
    refine ⟨_, .whilePropagate guard nonzero clock notBreak notContinue r1, fun c => ?_⟩
    have := l1 c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | whileInvalidGuard guard invalid =>
    cases hq; subst hf; exact ⟨_, .whileInvalidGuard guard invalid, SimpWorkLe.refl _⟩
  | _ => cases hq

theorem simpOk_call_runs {F : Type} (g : ProgHOL 64 → ProgHOL 64) {info function arguments}
    (hh : ∀ returns exception handlerVar handler,
      info = some (returns, some (exception, handlerVar, handler)) →
      SimpRunLeOk fn (F := F) handler (g handler)) :
    SimpRunLeOk fn (F := F) (.call info function arguments)
      (.call (simpMapInfo g info) function arguments) := by
  intro s r post ev run ok
  cases run with
  | callDone args lookup clock bodyRun plan =>
    refine ⟨_, .callDone args lookup clock bodyRun (simp_plan_map_done g plan), ?_⟩
    rw [callGlobalEvents_simpMapInfo]
    exact SimpWorkLe.refl _
  | callHandler args lookup clock bodyRun plan handlerRun =>
    obtain ⟨plan', returns, exception, handlerVar, hinfo⟩ := simp_plan_map_handler g plan
    obtain ⟨e, r', le⟩ := hh returns exception handlerVar _ hinfo handlerRun ok
    refine ⟨_, .callHandler args lookup clock bodyRun plan' r', fun c => ?_⟩
    have := le c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | callArgumentsFailure args => exact ⟨_, .callArgumentsFailure args, SimpWorkLe.refl _⟩
  | callLookupFailure args lookup => exact ⟨_, .callLookupFailure args lookup, SimpWorkLe.refl _⟩
  | callTimeout args lookup clock =>
    refine ⟨_, .callTimeout args lookup clock, ?_⟩
    rw [callGlobalEvents_simpMapInfo]
    exact SimpWorkLe.refl _

theorem simpOk_decCall_runs {F : Type} {name shape function arguments} {cont cont' : ProgHOL 64}
    (hc : SimpRunLeOk fn (F := F) cont cont') :
    SimpRunLeOk fn (F := F) (.decCall name shape function arguments cont)
      (.decCall name shape function arguments cont') := by
  intro s r post ev run ok
  cases run with
  | declareCallReturn args lookup clock bodyRun shapeMatch continuationRun =>
    obtain ⟨e, r', le⟩ := hc continuationRun ok
    refine ⟨_, .declareCallReturn args lookup clock bodyRun shapeMatch r', fun c => ?_⟩
    have := le c
    simp only [eventSum_cons, eventSum_append] at *
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

theorem simpOk_dec_runs {F : Type} {name shape value} {body body' : ProgHOL 64}
    (hb : SimpRunLeOk fn (F := F) body body') :
    SimpRunLeOk fn (F := F) (.dec name shape value body) (.dec name shape value body') := by
  intro s r post ev run ok
  cases run with
  | declareValue init shapeMatch bodyRun =>
    obtain ⟨e, r', le⟩ := hb bodyRun ok
    refine ⟨_, .declareValue init shapeMatch r', fun c => ?_⟩
    have := le c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | declareMismatch init mismatch => exact ⟨_, .declareMismatch init mismatch, SimpWorkLe.refl _⟩
  | declareFailure init => exact ⟨_, .declareFailure init, SimpWorkLe.refl _⟩

theorem simpOk_ite_runs {F : Type} {condition} {yes yes' no no' : ProgHOL 64}
    (hy : SimpRunLeOk fn (F := F) yes yes') (hn : SimpRunLeOk fn (F := F) no no') :
    SimpRunLeOk fn (F := F) (.ite condition yes no) (.ite condition yes' no') := by
  intro s r post ev run ok
  cases run with
  | iteYes guard nonzero body =>
    obtain ⟨e, r', le⟩ := hy body ok
    refine ⟨_, .iteYes guard nonzero r', fun c => ?_⟩
    have := le c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | iteNo guard body =>
    obtain ⟨e, r', le⟩ := hn body ok
    refine ⟨_, .iteNo guard r', fun c => ?_⟩
    have := le c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | iteInvalidGuard guard invalid => exact ⟨_, .iteInvalidGuard guard invalid, SimpWorkLe.refl _⟩

theorem simpOk_seq_runs {F : Type} {a a' b b' : ProgHOL 64}
    (ha : SimpRunLeOk fn (F := F) a a') (hb : SimpRunLeOk fn (F := F) b b') :
    SimpRunLeOk fn (F := F) (.seq a b) (.seq a' b') := by
  intro s r post ev run ok
  cases run with
  | seqNext one two =>
    obtain ⟨e1, r1, l1⟩ := ha one (by simp)
    obtain ⟨e2, r2, l2⟩ := hb two ok
    refine ⟨_, .seqNext r1 r2, fun c => ?_⟩
    have := l1 c; have := l2 c
    simp only [eventSum_cons, eventSum_append] at *
    omega
  | seqStop terminal one =>
    obtain ⟨e1, r1, l1⟩ := ha one ok
    refine ⟨_, .seqStop terminal r1, fun c => ?_⟩
    have := l1 c
    try simp only [eventSum_cons] at *
    omega

/-- A call without handler has a `done` plan. -/
theorem simp_plan_noHandler {F : Type} {s : PanSemStateFiniteExact 64 F} {returns}
    {returnShape bodyResult} {bodyPost : PanSemStateFiniteExact 64 F} {info}
    (hinfo : info = none ∨ info = some (returns, none)) :
    ∃ r p, callCostPlan s info returnShape bodyResult bodyPost = .done r p := by
  cases hplan : callCostPlan s info returnShape bodyResult bodyPost with
  | done r p => exact ⟨r, p, rfl⟩
  | handler entry program =>
    obtain ⟨-, _, _, _, h⟩ := simp_plan_map_handler id hplan
    rcases hinfo with rfl | rfl <;> simp at h

/-- The tail-call rewrite of `seq_call_ret`, on a non-error run. -/
theorem simp_tail_run {F : Type} (returnName : MlStringHOL) (function : MlStringHOL)
    (arguments : List (ExpHOL 64)) :
    SimpRunLeOk fn (F := F)
      (.seq (.call (some (some (.local, returnName), none)) function arguments)
        (.return (.var .local returnName)))
      (.call none function arguments) := by
  intro s r post ev run ok
  have sem : evaluateHOLFiniteState s (.call none function arguments) = (r, post) := by
    have h := PanSimp.RetToTailCorrect.evaluateSeqCallRetEqHOL
      (.seq (.call (some (some (.local, returnName), none)) function arguments)
        (.return (.var .local returnName))) s (by rw [run.sound]; exact ok)
    rw [run.sound] at h
    simpa [seqCallRetHOL] using h
  -- the original call run, in either sequence rule
  have callPart : ∃ r1 post1 left, StatementRun fn s
      (.call (some (some (.local, returnName), none)) function arguments) r1 post1 left ∧
      r1 ≠ some .error ∧ SimpWorkLe left ev := by
    cases run with
    | seqNext one two =>
      refine ⟨_, _, _, one, by simp, fun c => ?_⟩
      simp only [eventSum_append]; omega
    | seqStop terminal one =>
      refine ⟨_, _, _, one, ok, fun c => ?_⟩
      try simp only [eventSum_cons]
      omega
  obtain ⟨r1, post1, left, one, ok1, le⟩ := callPart
  cases one with
  | callDone args lookup clock bodyRun plan =>
    obtain ⟨r', p', plan'⟩ := simp_plan_noHandler (info := none) (returns := none)
      (s := s) (returnShape := _) (bodyResult := _) (bodyPost := _) (Or.inl rfl)
    have tail := StatementRun.callDone (fn := fn) (info := none) args lookup clock bodyRun plan'
    have hs := tail.sound
    rw [sem] at hs
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, tail, le⟩
  | callHandler args lookup clock bodyRun plan handlerRun =>
    obtain ⟨-, _, _, _, h⟩ := simp_plan_map_handler id plan
    simp at h
  | callArgumentsFailure args => exact absurd rfl ok1
  | callLookupFailure args lookup => exact absurd rfl ok1
  | callTimeout args lookup clock =>
    have tail := StatementRun.callTimeout (fn := fn) (info := none) args lookup clock
    have hs := tail.sound
    rw [sem] at hs
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, tail, le⟩

theorem simp_seqCallRet_run {F : Type} (a b : ProgHOL 64) :
    SimpRunLeOk fn (F := F) (.seq a b) (seqCallRetHOL (.seq a b)) := by
  by_cases hshape : ∃ returnName function arguments,
      a = .call (some (some (.local, returnName), none)) function arguments ∧
        b = .return (.var .local returnName)
  · obtain ⟨returnName, function, arguments, rfl, rfl⟩ := hshape
    have e : seqCallRetHOL (ProgHOL.seq (.call (some (some (.local, returnName), none)) function
        arguments) (.return (.var .local returnName))) = .call none function arguments := by
      simp [seqCallRetHOL]
    rw [e]
    exact simp_tail_run returnName function arguments
  · have e : seqCallRetHOL (.seq a b) = .seq a b := by
      unfold seqCallRetHOL
      split
      · rename_i x returnName function arguments returnedName heq
        simp only [ProgHOL.seq.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        split
        · rename_i h
          subst h
          exact absurd ⟨returnName, function, arguments, rfl, rfl⟩ hshape
        · rfl
      · first | rfl | simp_all
    rw [e]
    exact fun run _ => ⟨_, run, SimpWorkLe.refl _⟩

theorem SimpRunLeOk.trans {F : Type} {a b c : ProgHOL 64} (h1 : SimpRunLeOk fn (F := F) a b)
    (h2 : SimpRunLeOk fn (F := F) b c) : SimpRunLeOk fn (F := F) a c := by
  intro s r post ev run ok
  obtain ⟨e1, r1, l1⟩ := h1 run ok
  obtain ⟨e2, r2, l2⟩ := h2 r1 ok
  exact ⟨e2, r2, l2.trans l1⟩

theorem SimpRunLeOk.refl {F : Type} (a : ProgHOL 64) : SimpRunLeOk fn (F := F) a a :=
  fun run _ => ⟨_, run, SimpWorkLe.refl _⟩

/-- `ret_to_tail` never increases executed source work on non-error runs. -/
theorem simp_retToTail_run {F : Type} : ∀ p : ProgHOL 64, SimpRunLeOk fn (F := F) p (retToTailHOL p)
  | .seq a b => by
    have e : retToTailHOL (.seq a b) = seqCallRetHOL (.seq (retToTailHOL a) (retToTailHOL b)) := by
      rw [retToTailHOL]
    rw [e]
    exact SimpRunLeOk.trans (simpOk_seq_runs (simp_retToTail_run a) (simp_retToTail_run b))
      (simp_seqCallRet_run _ _)
  | .dec name shape value body => by
    have e : retToTailHOL (.dec name shape value body) =
        .dec name shape value (retToTailHOL body) := by rw [retToTailHOL]
    rw [e]; exact simpOk_dec_runs (simp_retToTail_run body)
  | .ite condition yes no => by
    have e : retToTailHOL (.ite condition yes no) =
        .ite condition (retToTailHOL yes) (retToTailHOL no) := by rw [retToTailHOL]
    rw [e]; exact simpOk_ite_runs (simp_retToTail_run yes) (simp_retToTail_run no)
  | .while condition body => by
    have e : retToTailHOL (.while condition body) =
        .while condition (retToTailHOL body) := by rw [retToTailHOL]
    rw [e]; exact simpOk_while_runs (simp_retToTail_run body)
  | .decCall name shape function arguments body => by
    have e : retToTailHOL (.decCall name shape function arguments body) =
        .decCall name shape function arguments (retToTailHOL body) := by rw [retToTailHOL]
    rw [e]; exact simpOk_decCall_runs (simp_retToTail_run body)
  | .call none function arguments => by
    have e : retToTailHOL (.call none function arguments) =
        .call (simpMapInfo retToTailHOL none) function arguments := by rw [retToTailHOL]; rfl
    rw [e]; exact simpOk_call_runs _ (fun _ _ _ _ h => by cases h)
  | .call (some (returns, none)) function arguments => by
    have e : retToTailHOL (.call (some (returns, none)) function arguments) =
        .call (simpMapInfo retToTailHOL (some (returns, none))) function arguments := by
      rw [retToTailHOL]; rfl
    rw [e]; exact simpOk_call_runs _ (fun _ _ _ _ h => by cases h)
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments => by
    have e : retToTailHOL (.call (some (returns, some (exception, handlerVar, handler)))
          function arguments) =
        .call (simpMapInfo retToTailHOL (some (returns, some (exception, handlerVar, handler))))
          function arguments := by
      rw [retToTailHOL]; rfl
    have ih : SimpRunLeOk fn (F := F) handler (retToTailHOL handler) := simp_retToTail_run handler
    have hh : ∀ returns' exception' handlerVar' handler',
        some (returns, some (exception, handlerVar, handler)) =
          some (returns', some (exception', handlerVar', handler')) →
        SimpRunLeOk fn (F := F) handler' (retToTailHOL handler') := by
      intro r' e' v' h' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, -, -, rfl⟩ := heq
      exact ih
    rw [e]; exact simpOk_call_runs _ hh
  | .skip => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .assign kind name value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .primitive name operator args => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .store address value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .store32 address value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .storeByte address value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .break => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .continue => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .extCall function configuration configurationLength array arrayLength => by
    unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .raise exception value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .return value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .shMemLoad size kind name address => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .shMemStore size address value => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .tick => by unfold retToTailHOL; exact SimpRunLeOk.refl _
  | .annot tag text => by unfold retToTailHOL; exact SimpRunLeOk.refl _
termination_by p => sizeOf p

#print axioms simp_tail_run
#print axioms simp_seqCallRet_run
#print axioms simp_retToTail_run
end InitECandidate.Runtime.FineCost
