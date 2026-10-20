import InitECandidate.Runtime.SourceCostLoopPricing
import InitECandidate.Runtime.SourceCostCrepSimp
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assembly
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Executed-work transfer across `crep_arith$simp_prog`, the per-function
Crep-to-Crep pass that `crep_to_loop$compile_prog` applies before
`compile`. The pinned `crepArithSimpProgCorrect` is a lockstep simulation
(same result, same final state up to the mapped code), so the transfer is an
induction on `CrepWorkS` that never needs a clock extension. -/

theorem crepSimp_node_pos_sharp (e : CrepExpHOL 64) : 2 ≤ loopNodePrice e := loopNodePrice_pos e

theorem crepSimp_mulConst_work_sharp (x : CrepExpHOL 64) (c : BitVec 64) :
    loopNodePrice (crepMulConstHOL x c) ≤ 5 + loopNodePrice x := by
  unfold crepMulConstHOL
  split
  · simp only [loopNodePrice]; omega
  · split
    · omega
    · split
      · simp only [loopNodePrice, loopPriceList]; omega
      · simp only [loopNodePrice, loopPriceList]; omega

theorem crepSimp_list_work_sharp (es : List (CrepExpHOL 64))
    (ih : ∀ e ∈ es, loopNodePrice (crepSimpExpHOL e) ≤ loopNodePrice e) :
    sharpCrepList (es.map crepSimpExpHOL) ≤ sharpCrepList es := by
  induction es with
  | nil => simp [sharpCrepList, loopPriceList]
  | cons head tail ihTail =>
    have h1 := ih head (by simp)
    have h2 := ihTail (fun e h => ih e (by simp [h]))
    simp only [List.map_cons, sharpCrepList, loopPriceList, List.length_cons, List.length_map] at h2 ⊢
    omega

/-- `simp_exp` never increases the scalar node work of an expression. -/
theorem crepSimp_node_work_sharp : ∀ e : CrepExpHOL 64, loopNodePrice (crepSimpExpHOL e) ≤ loopNodePrice e
  | .crepOp op es => by
    have ih : ∀ e ∈ es, loopNodePrice (crepSimpExpHOL e) ≤ loopNodePrice e :=
      fun e _ => crepSimp_node_work_sharp e
    have listIh := crepSimp_list_work_sharp es ih
    cases op
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · unfold crepSimpExpHOL; simp only [List.map_nil]; exact Nat.le_refl _
    · unfold crepSimpExpHOL; simp only [List.map_cons, List.map_nil]
      have := ih a (by simp)
      simp only [loopNodePrice, sharpCrepList, loopPriceList] at this ⊢; omega
    · have ha := ih a (by simp)
      have hb := ih b (by simp)
      have pa := crepSimp_node_pos_sharp a
      have pb := crepSimp_node_pos_sharp b
      unfold crepSimpExpHOL
      simp only [List.map_cons, List.map_nil]
      split
      · simp only [loopNodePrice, sharpCrepList, loopPriceList]; omega
      · have := crepSimp_mulConst_work_sharp (crepSimpExpHOL b) ‹_›
        simp only [loopNodePrice, sharpCrepList, loopPriceList] at this ⊢; omega
      · have := crepSimp_mulConst_work_sharp (crepSimpExpHOL a) ‹_›
        simp only [loopNodePrice, sharpCrepList, loopPriceList] at this ⊢; omega
      · simp only [loopNodePrice, sharpCrepList, loopPriceList]; omega
    · unfold crepSimpExpHOL
      simp only [List.map_cons]
      simp only [loopNodePrice, List.map_cons, sharpCrepList, List.length_map, List.length_cons] at listIh ⊢
      omega
  | .load a => by
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    have := crepSimp_node_work_sharp a; omega
  | .load32 a => by
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    have := crepSimp_node_work_sharp a; omega
  | .loadByte a => by
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    have := crepSimp_node_work_sharp a; omega
  | .op op es => by
    have ih : ∀ e ∈ es, loopNodePrice (crepSimpExpHOL e) ≤ loopNodePrice e :=
      fun e _ => crepSimp_node_work_sharp e
    have := crepSimp_list_work_sharp es ih
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    simp only [sharpCrepList, List.length_map] at this; omega
  | .cmp op a b => by
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    have := crepSimp_node_work_sharp a; have := crepSimp_node_work_sharp b; omega
  | .shift op a b => by
    rw [crepSimpExpHOL]; simp only [loopNodePrice]
    have := crepSimp_node_work_sharp a; have := crepSimp_node_work_sharp b; omega
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by unfold crepSimpExpHOL; exact Nat.le_refl _
termination_by e => sizeOf e
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

theorem crepSimp_listWork_sharp (es : List (CrepExpHOL 64)) :
    sharpCrepList (es.map crepSimpExpHOL) ≤ sharpCrepList es :=
  crepSimp_list_work_sharp es (fun e _ => crepSimp_node_work_sharp e)

theorem crepSimp_exp_sharp {F : Type} (t : CrepSemHOLState 64 F) (e : CrepExpHOL 64)
    (v : HolWordLab 64) (h : evalCrepSemHOLExp t e = some v) :
    evalCrepSemHOLExp (crepSimpMapcsHOL t) (crepSimpExpHOL e) = some v := by
  rw [crepSimpMapcsHOL_eq_mapc]
  exact crepSimpExpCorrectNativeHOL _ t e v h

theorem crepSimp_args_sharp {F : Type} (t : CrepSemHOLState 64 F) :
    ∀ (es : List (CrepExpHOL 64)) (vs : List (HolWordLab 64)),
      es.mapM (evalCrepSemHOLExp t) = some vs →
      (es.map crepSimpExpHOL).mapM (evalCrepSemHOLExp (crepSimpMapcsHOL t)) = some vs
  | [], vs, h => by simpa using h
  | e :: es, vs, h => by
    simp only [List.mapM_cons, List.map_cons] at h ⊢
    cases he : evalCrepSemHOLExp t e with
    | none => simp [he] at h
    | some v =>
      cases hes : es.mapM (evalCrepSemHOLExp t) with
      | none => simp [he, hes] at h
      | some vs' =>
        simp only [he, hes] at h
        simp at h
        subst h
        simp [crepSimp_exp_sharp t e v he, crepSimp_args_sharp t es vs' hes]

/-- `lookup_code` on the `simp_prog`-mapped code (copy of the pinned private
`lookupCodeFiniteHOL_mapcs`). -/
theorem crepSimp_lookup_sharp {F : Type} (state : CrepSemHOLState 64 F)
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab 64)) (len : Nat) :
    lookupCodeFiniteHOL (crepSimpMapcsHOL state).code fname args len =
      (lookupCodeFiniteHOL state.code fname args len).map (Prod.map crepSimpProgHOL id) := by
  unfold lookupCodeFiniteHOL crepSimpMapcsHOL
  simp only [HolFiniteMapExact.lookup_map2]
  cases state.code.lookup fname with
  | none => rfl
  | some entry =>
      obtain ⟨parameters, body⟩ := entry
      simp only [Option.map_some]
      split <;> rfl

/-- Executed-work transfer across `crep_arith$simp_prog`: every non-error Crep
execution of `p` from `t` is matched by an execution of `crepSimpProgHOL p` from
the code-mapped state with no more `CrepWorkS`. -/
theorem crep_simp_work_sharp {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (work : CrepWorkS t p w) :
    (evalCrepSemHOLProgExact t p).1 ≠ some .error →
    ∃ w', CrepWorkS (crepSimpMapcsHOL t) (crepSimpProgHOL p) w' ∧ w' ≤ w := by
  induction work with
  | skip t => intro _; exact ⟨2, by unfold crepSimpProgHOL; exact .skip _, Nat.le_refl _⟩
  | tick t => intro _; exact ⟨2, by unfold crepSimpProgHOL; exact .tick _, Nat.le_refl _⟩
  | breakStmt t label =>
    intro _; exact ⟨2, by unfold crepSimpProgHOL; exact .breakStmt _ _, Nat.le_refl _⟩
  | continueStmt t label =>
    intro _; exact ⟨2, by unfold crepSimpProgHOL; exact .continueStmt _ _, Nat.le_refl _⟩
  | raise t code => intro _; exact ⟨3, by unfold crepSimpProgHOL; exact .raise _ _, Nat.le_refl _⟩
  | extCall t function configuration configurationLength array arrayLength =>
    intro _; exact ⟨2, by unfold crepSimpProgHOL; exact .extCall _ _ _ _ _ _, Nat.le_refl _⟩
  | primitive t names operator args =>
    intro _
    exact ⟨2 + names.length + args.length, by unfold crepSimpProgHOL; exact .primitive _ _ _ _,
      Nat.le_refl _⟩
  | assign t name value =>
    intro _
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL value), by simp only [crepSimpProgHOL]; exact .assign _ _ _,
      by omega⟩
  | storeGlob t address value =>
    intro _
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL value),
      by simp only [crepSimpProgHOL]; exact .storeGlob _ _ _, by omega⟩
  | shMem t operator name address =>
    intro _
    have := crepSimp_node_work_sharp address
    exact ⟨2 + loopNodePrice (crepSimpExpHOL address),
      by simp only [crepSimpProgHOL]; exact .shMem _ _ _ _, by omega⟩
  | store t address value =>
    intro _
    have := crepSimp_node_work_sharp address
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL address) + loopNodePrice (crepSimpExpHOL value),
      by simp only [crepSimpProgHOL]; exact .store _ _ _, by omega⟩
  | store32 t address value =>
    intro _
    have := crepSimp_node_work_sharp address
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL address) + loopNodePrice (crepSimpExpHOL value),
      by simp only [crepSimpProgHOL]; exact .store32 _ _ _, by omega⟩
  | storeByte t address value =>
    intro _
    have := crepSimp_node_work_sharp address
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL address) + loopNodePrice (crepSimpExpHOL value),
      by simp only [crepSimpProgHOL]; exact .storeByte _ _ _, by omega⟩
  | returnStmt t values =>
    intro _
    have := crepSimp_listWork_sharp values
    exact ⟨2 + sharpCrepList (values.map crepSimpExpHOL) + (values.map crepSimpExpHOL).length,
      by simp only [crepSimpProgHOL]; exact .returnStmt _ _, by simp only [List.length_map]; omega⟩
  | @decFailure t name value body failed =>
    intro ok
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_dec_holShape, failed]
  | @dec t name value body word bodyWork evaluated bodyRun ih =>
    intro ok
    have bodyOk : (evalCrepSemHOLProgExact { t with locals := t.locals.updateEq (name, word) }
        body).1 ≠ some .error := by
      intro h
      apply ok
      rw [evalCrepSemHOLProgExact_dec_holShape, evaluated]
      simp only
      exact h
    obtain ⟨wb, hb, bb⟩ := ih bodyOk
    have := crepSimp_node_work_sharp value
    exact ⟨2 + loopNodePrice (crepSimpExpHOL value) + wb,
      by simp only [crepSimpProgHOL]; exact .dec (crepSimp_exp_sharp t value word evaluated) hb, by omega⟩
  | @seqNext t first second middle firstWork secondWork one run two ihOne ihTwo =>
    intro ok
    have okTwo : (evalCrepSemHOLProgExact middle second).1 ≠ some .error := by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      simpa using okSeq
    obtain ⟨w1, h1, b1⟩ := ihOne (by rw [run]; simp)
    obtain ⟨w2, h2, b2⟩ := ihTwo okTwo
    have run' := crepArithSimpProgCorrect first t none middle run (by simp)
    exact ⟨w1 + w2, by simp only [crepSimpProgHOL]; exact .seqNext h1 run' h2, by omega⟩
  | @seqStop t first second result middle firstWork one run ihOne =>
    intro ok
    have okOne : (evalCrepSemHOLProgExact t first).1 ≠ some .error := by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      rw [run]; simpa using okSeq
    obtain ⟨w1, h1, b1⟩ := ihOne okOne
    have run' := crepArithSimpProgCorrect first t (some result) middle run
      (by rw [run] at okOne; exact okOne)
    exact ⟨w1, by simp only [crepSimpProgHOL]; exact .seqStop h1 run', by omega⟩
  | @iteBranch t condition yes no word branchWork guard branch ihBranch =>
    intro ok
    have okBranch : (evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no)).1 ≠ some .error := by
      rw [evalCrepSemHOLProgExact_ite_holShape, guard] at ok; exact ok
    obtain ⟨wb, hb, bb⟩ := ihBranch okBranch
    rw [apply_ite crepSimpProgHOL] at hb
    have := crepSimp_node_work_sharp condition
    exact ⟨2 + loopNodePrice (crepSimpExpHOL condition) + wb,
      by simp only [crepSimpProgHOL]; exact .iteBranch (crepSimp_exp_sharp t condition _ guard) hb,
      by omega⟩
  | @iteInvalid t condition yes no invalid =>
    intro ok
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_ite_holShape]
    split
    · rename_i w hw; exact absurd hw (invalid w)
    · rfl
  | @whileExit t condition body exit =>
    intro ok
    cases hev : evalCrepSemHOLExp t condition with
    | none =>
      exfalso; apply ok; rw [evalCrepSemHOLProgExact_while_holShape, hev]
    | some v =>
      cases v with
      | word w0 =>
        have hw := exit w0 hev
        have hev' := crepSimp_exp_sharp t condition _ hev
        have := crepSimp_node_work_sharp condition
        refine ⟨2 + 2 + loopNodePrice (crepSimpExpHOL condition), ?_, by omega⟩
        simp only [crepSimpProgHOL]
        refine .whileExit (fun word h => ?_)
        rw [hev'] at h
        simp only [Option.some.injEq, HolWordLab.word.injEq] at h
        rw [← h]; exact hw
  | @whileTimeout t condition body word guard nonzero clock =>
    intro _
    have := crepSimp_node_work_sharp condition
    exact ⟨2 + 2 + loopNodePrice (crepSimpExpHOL condition),
      by simp only [crepSimpProgHOL]; exact .whileTimeout (crepSimp_exp_sharp t condition _ guard) nonzero clock,
      by omega⟩
  | @whileLoop t condition body word bodyWork result middle restWork guard nonzero clock one run
      again rest ihOne ihRest =>
    intro ok
    have bodyOk : result ≠ some .error := by
      rintro rfl
      apply ok
      rw [evalCrepSemHOLProgExact_while_holShape, guard]
      simp only [ne_eq, clock, if_false]
      rw [if_pos nonzero, run]
      rfl
    have restOk : (evalCrepSemHOLProgExact middle (.while condition body)).1 ≠ some .error := by
      have crepRun : evalCrepSemHOLProgExact t (.while condition body) =
          evalCrepSemHOLProgExact middle (.while condition body) := by
        rw [evalCrepSemHOLProgExact_while_holShape, guard]
        simp only [ne_eq, clock, if_false]
        rw [if_pos nonzero, run]
        rcases again with rfl | rfl <;> rfl
      rw [← crepRun]; exact ok
    obtain ⟨wb, hb, bb⟩ := ihOne (by rw [run]; exact bodyOk)
    obtain ⟨wr, hr, br⟩ := ihRest restOk
    have run' := crepArithSimpProgCorrect body _ result middle run bodyOk
    simp only [crepSimpProgHOL] at hr
    have := crepSimp_node_work_sharp condition
    exact ⟨2 + 2 + loopNodePrice (crepSimpExpHOL condition) + wb + wr,
      by simp only [crepSimpProgHOL]
         exact .whileLoop (crepSimp_exp_sharp t condition _ guard) nonzero clock hb run' again hr,
      by omega⟩
  | @whileStop t condition body word bodyWork result middle guard nonzero clock one run stop
      ihOne =>
    intro ok
    have bodyOk : result ≠ some .error := by
      rintro rfl
      apply ok
      rw [evalCrepSemHOLProgExact_while_holShape, guard]
      simp only [ne_eq, clock, if_false]
      rw [if_pos nonzero, run]
      rfl
    obtain ⟨wb, hb, bb⟩ := ihOne (by rw [run]; exact bodyOk)
    have run' := crepArithSimpProgCorrect body _ result middle run bodyOk
    have := crepSimp_node_work_sharp condition
    exact ⟨2 + 2 + loopNodePrice (crepSimpExpHOL condition) + wb,
      by simp only [crepSimpProgHOL]
         exact .whileStop (crepSimp_exp_sharp t condition _ guard) nonzero clock hb run' stop,
      by omega⟩
  | @callShort t returnInfo function arguments short =>
    intro ok
    have := crepSimp_listWork_sharp arguments
    rcases short with hnone | ⟨values, hvals, hl | hn | hc⟩
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hnone]
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hvals]
      split
      · rename_i args hargs; cases hargs; rw [hl]
      · rfl
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hvals]
      split
      · rename_i args hargs; cases hargs
        split
        · rw [if_pos hn]
        · rfl
      · rfl
    · refine ⟨2 + 2 + 2 + sharpCrepList (arguments.map crepSimpExpHOL), ?_, by omega⟩
      unfold crepSimpProgHOL
      exact .callShort (Or.inr ⟨_, crepSimp_args_sharp t _ _ hvals, Or.inr (Or.inr hc)⟩)
  | @callBody t returnInfo function arguments values body locals bodyWork result post args lookup
      names clock bodyRun run unhandled ihBody =>
    intro ok
    have bodyOk : result ≠ some .error := by
      rintro rfl
      apply ok
      rw [evalCrepSemHOLProgExact_call_holShape, args]
      simp only
      rw [lookup]
      split
      · rename_i prog nl heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [if_neg names, if_neg clock, run]
      · rename_i heq; exact absurd heq (by simp)
    obtain ⟨wb, hb, bb⟩ := ihBody (by rw [run]; exact bodyOk)
    have run' := crepArithSimpProgCorrect body _ result post run bodyOk
    have args' := crepSimp_args_sharp t arguments values args
    have lookup' : lookupCodeFiniteHOL (crepSimpMapcsHOL t).code function values values.length =
        some (crepSimpProgHOL body, locals) := by
      rw [crepSimp_lookup_sharp, lookup]; rfl
    have := crepSimp_listWork_sharp arguments
    refine ⟨2 + 2 + 2 + sharpCrepList (arguments.map crepSimpExpHOL) + values.length + wb +
      crepCallPayloadWords result, ?_, by omega⟩
    unfold crepSimpProgHOL
    refine .callBody args' lookup' ?_ clock hb run' ?_
    · rcases returnInfo with _ | ⟨rts, _ | ⟨c, h⟩⟩ <;>
        simpa [crepReturnInfoNodupError] using names
    · intro code rts handler hres
      rcases returnInfo with _ | ⟨rts0, _ | ⟨c0, h0⟩⟩
      · simp
      · simp
      · simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
        rintro rfl rfl _
        exact unhandled _ _ _ hres rfl
  | @callHandler t rts code handler function arguments values body locals bodyWork post
      handlerWork args lookup names clock bodyRun run handlerRun ihBody ihHandler =>
    intro ok
    have handlerOk : (evalCrepSemHOLProgExact { post with locals := t.locals } handler).1 ≠
        some .error := by
      intro h
      apply ok
      rw [evalCrepSemHOLProgExact_call_holShape, args]
      simp only
      rw [lookup]
      have hnd : ¬ crepReturnInfoNodupError
          (some (rts, some (code, handler)) : Option (List Nat × Option (BitVec 64 × CrepProgHOL 64))) := by
        simpa [crepReturnInfoNodupError] using names
      simp only [hnd, clock, if_false, run, if_true]
      exact h
    obtain ⟨wb, hb, bb⟩ := ihBody (by rw [run]; simp)
    obtain ⟨wh, hh, bh⟩ := ihHandler handlerOk
    have run' := crepArithSimpProgCorrect body _ _ post run (by simp)
    have args' := crepSimp_args_sharp t arguments values args
    have lookup' : lookupCodeFiniteHOL (crepSimpMapcsHOL t).code function values values.length =
        some (crepSimpProgHOL body, locals) := by
      rw [crepSimp_lookup_sharp, lookup]; rfl
    have := crepSimp_listWork_sharp arguments
    refine ⟨2 + 2 + 2 + sharpCrepList (arguments.map crepSimpExpHOL) + values.length + wb + wh, ?_, by omega⟩
    simp only [crepSimpProgHOL]
    exact .callHandler args' lookup' names clock hb run' hh

#print axioms crepSimp_node_work_sharp
#print axioms crepSimp_listWork_sharp
#print axioms crep_simp_work_sharp
end InitECandidate.Runtime.FineCost
