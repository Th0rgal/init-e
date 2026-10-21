import InitECandidate.Runtime.CrepWorkF
import InitECandidate.Runtime.SourceCostSharpCrepSimp
import InitECandidate.Runtime.PanSourcePriceDef
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Executed-work transfer across `crep_arith$simp_prog` for function-indexed
Crep work at any prices that `simp_exp` does not increase. -/

section
variable {price : CrepExpHOL 64 → Nat} {priceList : List (CrepExpHOL 64) → Nat} {K : StmtK}
  {callP : CName → CName → Nat → Nat} {shortP : Nat}

theorem CrepWorkF.simp {F : Type} {fn : CName} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64} {w : Nat}
    (hp : ∀ e, price (crepSimpExpHOL e) ≤ price e)
    (hl : ∀ es, priceList (es.map crepSimpExpHOL) ≤ priceList es)
    (work : CrepWorkF price priceList K callP shortP fn t p w) :
    (evalCrepSemHOLProgExact t p).1 ≠ some .error →
    ∃ w', CrepWorkF price priceList K callP shortP fn (crepSimpMapcsHOL t) (crepSimpProgHOL p) w' ∧ w' ≤ w := by
  induction work with
  | skip fn t => intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .skip _ _, Nat.le_refl _⟩
  | tick fn t => intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .tick _ _, Nat.le_refl _⟩
  | breakStmt fn t label =>
    intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .breakStmt _ _ _, Nat.le_refl _⟩
  | continueStmt fn t label =>
    intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .continueStmt _ _ _, Nat.le_refl _⟩
  | raise fn t code => intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .raise _ _ _, Nat.le_refl _⟩
  | extCall fn t function configuration configurationLength array arrayLength =>
    intro _; exact ⟨_, by unfold crepSimpProgHOL; exact .extCall _ _ _ _ _ _ _, Nat.le_refl _⟩
  | primitive fn t names operator args =>
    intro _
    exact ⟨_, by unfold crepSimpProgHOL; exact .primitive _ _ _ _ _,
      Nat.le_refl _⟩
  | assign fn t name value =>
    intro _
    have := hp value
    exact ⟨_, by simp only [crepSimpProgHOL]; exact .assign _ _ _ _,
      by omega⟩
  | storeGlob fn t address value =>
    intro _
    have := hp value
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .storeGlob _ _ _ _, by omega⟩
  | shMem fn t operator name address =>
    intro _
    have := hp address
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .shMem _ _ _ _ _, by omega⟩
  | store fn t address value =>
    intro _
    have := hp address
    have := hp value
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .store _ _ _ _, by omega⟩
  | store32 fn t address value =>
    intro _
    have := hp address
    have := hp value
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .store32 _ _ _ _, by omega⟩
  | storeByte fn t address value =>
    intro _
    have := hp address
    have := hp value
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .storeByte _ _ _ _, by omega⟩
  | returnStmt fn t values =>
    intro _
    have := hl values
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .returnStmt _ _ _, by simp only [List.length_map]; omega⟩
  | @decFailure fn t name value body failed =>
    intro ok
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_dec_holShape, failed]
  | @dec fn t name value body word bodyWork evaluated bodyRun ih =>
    intro ok
    have bodyOk : (evalCrepSemHOLProgExact { t with locals := t.locals.updateEq (name, word) }
        body).1 ≠ some .error := by
      intro h
      apply ok
      rw [evalCrepSemHOLProgExact_dec_holShape, evaluated]
      simp only
      exact h
    obtain ⟨wb, hb, bb⟩ := ih bodyOk
    have := hp value
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .dec (crepSimp_exp_sharp t value word evaluated) hb, by omega⟩
  | @seqNext fn t first second middle firstWork secondWork one run two ihOne ihTwo =>
    intro ok
    have okTwo : (evalCrepSemHOLProgExact middle second).1 ≠ some .error := by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      simpa using okSeq
    obtain ⟨w1, h1, b1⟩ := ihOne (by rw [run]; simp)
    obtain ⟨w2, h2, b2⟩ := ihTwo okTwo
    have run' := crepArithSimpProgCorrect first t none middle run (by simp)
    exact ⟨w1 + w2, by simp only [crepSimpProgHOL]; exact .seqNext h1 run' h2, by omega⟩
  | @seqStop fn t first second result middle firstWork one run ihOne =>
    intro ok
    have okOne : (evalCrepSemHOLProgExact t first).1 ≠ some .error := by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      rw [run]; simpa using okSeq
    obtain ⟨w1, h1, b1⟩ := ihOne okOne
    have run' := crepArithSimpProgCorrect first t (some result) middle run
      (by rw [run] at okOne; exact okOne)
    exact ⟨w1, by simp only [crepSimpProgHOL]; exact .seqStop h1 run', by omega⟩
  | @iteBranch fn t condition yes no word branchWork guard branch ihBranch =>
    intro ok
    have okBranch : (evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no)).1 ≠ some .error := by
      rw [evalCrepSemHOLProgExact_ite_holShape, guard] at ok; exact ok
    obtain ⟨wb, hb, bb⟩ := ihBranch okBranch
    rw [apply_ite crepSimpProgHOL] at hb
    have := hp condition
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .iteBranch (crepSimp_exp_sharp t condition _ guard) hb,
      by omega⟩
  | @iteInvalid fn t condition yes no invalid =>
    intro ok
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_ite_holShape]
    split
    · rename_i w hw; exact absurd hw (invalid w)
    · rfl
  | @whileExit fn t condition body exit =>
    intro ok
    cases hev : evalCrepSemHOLExp t condition with
    | none =>
      exfalso; apply ok; rw [evalCrepSemHOLProgExact_while_holShape, hev]
    | some v =>
      cases v with
      | word w0 =>
        have hw := exit w0 hev
        have hev' := crepSimp_exp_sharp t condition _ hev
        have := hp condition
        refine ⟨_, ?_, Nat.add_le_add_left this _⟩
        simp only [crepSimpProgHOL]
        refine .whileExit (fun word h => ?_)
        rw [hev'] at h
        simp only [Option.some.injEq, HolWordLab.word.injEq] at h
        rw [← h]; exact hw
  | @whileTimeout fn t condition body word guard nonzero clock =>
    intro _
    have := hp condition
    exact ⟨_,
      by simp only [crepSimpProgHOL]; exact .whileTimeout (crepSimp_exp_sharp t condition _ guard) nonzero clock,
      by omega⟩
  | @whileLoop fn t condition body word bodyWork result middle restWork guard nonzero clock one run
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
    have := hp condition
    exact ⟨_,
      by simp only [crepSimpProgHOL]
         exact .whileLoop (crepSimp_exp_sharp t condition _ guard) nonzero clock hb run' again hr,
      by omega⟩
  | @whileStop fn t condition body word bodyWork result middle guard nonzero clock one run stop
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
    have := hp condition
    exact ⟨_,
      by simp only [crepSimpProgHOL]
         exact .whileStop (crepSimp_exp_sharp t condition _ guard) nonzero clock hb run' stop,
      by omega⟩
  | @callShort fn t returnInfo function arguments short =>
    intro ok
    have := hl arguments
    rcases short with hnone | ⟨values, hvals, hlk | hn | hc⟩
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hnone]
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hvals]
      split
      · rename_i args hargs; cases hargs; rw [hlk]
      · rfl
    · exfalso; apply ok; rw [evalCrepSemHOLProgExact_call_holShape, hvals]
      split
      · rename_i args hargs; cases hargs
        split
        · rw [if_pos hn]
        · rfl
      · rfl
    · unfold crepSimpProgHOL
      refine ⟨_, CrepWorkF.callShort (Or.inr ⟨_, crepSimp_args_sharp t _ _ hvals, Or.inr (Or.inr hc)⟩), ?_⟩
      rcases returnInfo with _ | ⟨rts, _ | ⟨c, h⟩⟩ <;> simp only [crepRetCount, List.length_map] <;> omega
  | @callBody fn t returnInfo function arguments values body locals bodyWork result post args lookup
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
    have := hl arguments
    refine ⟨?w, ?work, ?bound⟩
    case work =>
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
    case bound =>
      rcases returnInfo with _ | ⟨rts, _ | ⟨c, h⟩⟩ <;> simp only [crepRetCount, List.length_map] <;> omega
  | @callHandler fn t rts code handler function arguments values body locals bodyWork post
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
    have := hl arguments
    refine ⟨_, by simp only [crepSimpProgHOL]; exact .callHandler args' lookup' names clock hb run' hh, ?_⟩
    simp only [List.length_map]; omega

end

/-! `simp_exp` never increases node-cost prices once a shift costs no more than
a Crep multiplication (a multiplication by a power of two becomes a shift). -/

section
variable {K : NodeK} (hK : K.shift ≤ K.crepOp)
include hK

theorem nodePriceK_mulConst (x : CrepExpHOL 64) (c : BitVec 64) :
    nodePriceK K (crepMulConstHOL x c) ≤ nodePriceK K x + K.cst + K.crepOp := by
  unfold crepMulConstHOL
  split
  · simp only [nodePriceK]; omega
  · split
    · omega
    · split
      · simp only [nodePriceK, nodePriceListK]; omega
      · simp only [nodePriceK]; omega

omit hK in
theorem nodePriceK_destConst {e : CrepExpHOL 64} {c : BitVec 64} (h : crepDestConstHOL e = some c) :
    nodePriceK K e = K.cst := by
  cases e <;> simp_all [crepDestConstHOL, nodePriceK]

omit hK in
theorem nodePriceListK_simp_of (es : List (CrepExpHOL 64))
    (ih : ∀ e ∈ es, nodePriceK K (crepSimpExpHOL e) ≤ nodePriceK K e) :
    nodePriceListK K (es.map crepSimpExpHOL) ≤ nodePriceListK K es := by
  induction es with
  | nil => simp [nodePriceListK]
  | cons head tail ihTail =>
    have h1 := ih head (by simp)
    have h2 := ihTail (fun e h => ih e (by simp [h]))
    simp only [List.map_cons, nodePriceListK] at h2 ⊢
    omega

theorem nodePriceK_simp : ∀ e : CrepExpHOL 64, nodePriceK K (crepSimpExpHOL e) ≤ nodePriceK K e
  | .crepOp op es => by
    have ih : ∀ e ∈ es, nodePriceK K (crepSimpExpHOL e) ≤ nodePriceK K e :=
      fun e _ => nodePriceK_simp e
    have listIh := nodePriceListK_simp_of es ih
    cases op
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · unfold crepSimpExpHOL; simp only [List.map_nil]; exact Nat.le_refl _
    · unfold crepSimpExpHOL; simp only [List.map_cons, List.map_nil]
      have := ih a (by simp)
      simp only [nodePriceK, nodePriceListK] at this ⊢; omega
    · have ha := ih a (by simp)
      have hb := ih b (by simp)
      unfold crepSimpExpHOL
      simp only [List.map_cons, List.map_nil]
      split
      · rename_i l r da db
        have := nodePriceK_destConst (K := K) da
        simp only [nodePriceK, nodePriceListK] at this ⊢; omega
      · rename_i constant da db
        have := nodePriceK_mulConst hK (crepSimpExpHOL b) constant
        have := nodePriceK_destConst (K := K) da
        simp only [nodePriceK, nodePriceListK] at this ⊢; omega
      · rename_i constant da db
        have := nodePriceK_mulConst hK (crepSimpExpHOL a) constant
        have := nodePriceK_destConst (K := K) db
        simp only [nodePriceK, nodePriceListK] at this ⊢; omega
      · simp only [nodePriceK, nodePriceListK]; omega
    · unfold crepSimpExpHOL
      simp only [List.map_cons]
      simp only [nodePriceK, List.map_cons, nodePriceListK] at listIh ⊢
      omega
  | .load a => by
    rw [crepSimpExpHOL]; simp only [nodePriceK]
    have := nodePriceK_simp a; omega
  | .load32 a => by
    rw [crepSimpExpHOL]; simp only [nodePriceK]
    have := nodePriceK_simp a; omega
  | .loadByte a => by
    rw [crepSimpExpHOL]; simp only [nodePriceK]
    have := nodePriceK_simp a; omega
  | .op op es => by
    have ih : ∀ e ∈ es, nodePriceK K (crepSimpExpHOL e) ≤ nodePriceK K e :=
      fun e _ => nodePriceK_simp e
    have := nodePriceListK_simp_of es ih
    rw [crepSimpExpHOL]; simp only [nodePriceK, List.length_map]; omega
  | .cmp op a b => by
    rw [crepSimpExpHOL]; simp only [nodePriceK]
    have := nodePriceK_simp a; have := nodePriceK_simp b; omega
  | .shift op a b => by
    rw [crepSimpExpHOL]; simp only [nodePriceK]
    have := nodePriceK_simp a; have := nodePriceK_simp b; omega
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by unfold crepSimpExpHOL; exact Nat.le_refl _
termination_by e => sizeOf e
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

theorem nodePriceListK_simp (es : List (CrepExpHOL 64)) :
    nodePriceListK K (es.map crepSimpExpHOL) ≤ nodePriceListK K es :=
  nodePriceListK_simp_of es (fun e _ => nodePriceK_simp hK e)

end

#print axioms nodePriceK_simp
#print axioms CrepWorkF.simp
end InitECandidate.Runtime.FineCost
