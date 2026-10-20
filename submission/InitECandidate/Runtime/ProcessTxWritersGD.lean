import InitECandidate.Runtime.ProcessTxPrefixGD
import InitECandidate.Runtime.OriginalBn254InitCode
/-!
The `process_transaction` sender-debit segment over the content-carrying registry: call rules for callees with
struct parameters (callee-entry scalar locals supplied by the caller), the actual `increment_nonce`,
`set_account_balance` and `u256_sub` calls keeping `PXR`, and the composition from `bal_index = index + 1` to the
`te_new()` declaration.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shape4' {v : ValueHOL 64} (h : shapeEqHOL (.comb [.one,.one,.one,.one]) (shapeOfHOLExact v) = true) :
    ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)] := by
  rcases v with ⟨⟨x⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨⟨⟨a⟩⟩ | _ | _,_ | ⟨⟨⟨b⟩⟩ | _ | _,_ | ⟨⟨⟨c⟩⟩ | _ | _,_ | ⟨⟨⟨d⟩⟩ | _ | _,_ | ⟨_,_⟩⟩⟩⟩⟩ <;>
      simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact,shapeEqHOL] at h

set_option maxRecDepth 100000 in
/-- Callee entry of the actual `set_account_balance(addr, amount)`: a one-word `addr`, a four-word `amount`, and
no other locals. -/
theorem setBal_callee {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "set_account_balance") values = some (body,callee,rs)) :
    SL (fun x => x ≠ ofString "amount") callee ∧ AmtL callee ∧
      ∃ A : BitVec 64, callee.lookup (ofString "addr") = some (.val (.word A)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs0 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [originalRuntimeCode_setAccountBalance_lookup] at found
    generalize sourceFunctionBody Guest.guestFn_set_account_balance = BB at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0,v1], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,
          Bool.and_eq_true] at hall
        obtain ⟨s0,s1⟩ := hall
        obtain ⟨a,rfl⟩ : ∃ a : BitVec 64, v0 = .val (.word a) := scalar_of_shape s0
        obtain ⟨b0,b1,b2,b3,rfl⟩ := shape4' s1
        subst hcl
        have ne : ofString "addr" ≠ ofString "amount" := by decide
        refine ⟨fun x hx v hv => ?_,⟨b0,b1,b2,b3,?_⟩,a,?_⟩
        · rw [hl] at hv
          simp [List.map_cons,List.zip_cons_cons,hx] at hv
          exact ⟨a,hv.2.symm⟩
        · rw [hl]; simp
        · rw [hl]; simp [ne]
    · cases found

#print axioms shape4'
#print axioms setBal_callee

section gen
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `aqgd_callSpec` with the callee-entry scalar locals supplied by the caller (any parameter shapes). -/
theorem aqgd_callSpecS {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hsl : ∀ values callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      SL Vn' callee)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hq : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q L M' H') :
    AQGD D B A w Vn P Q RR (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := hsl values callee foundShape lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          esl H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),fun _ => ⟨sl,H',hH',hq _ _ _ _ _ _ pre rr⟩,
                (fun v e => by cases e),by simp,by simp⟩)
            | exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- `aqgd_callAssignF` with the callee-entry scalar locals supplied by the caller (any parameter shapes). -/
theorem aqgd_callAssignFS {Vn' : MlS → Prop} {P Q : GA → Mem → GA → Prop}
    (Pe : GA → Mem → GA → GA → Mem → GA → Prop) (RRe : GA → Mem → GA → ValueHOL 64 → Mem → GA → Prop)
    (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hsl : ∀ values callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      SL Vn' callee) (hvn : ¬ Vn name)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q (L.update (name,v)) M' H') :
    AQGD D B A w Vn P Q RR (.call (some (some (.local,name),none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := hsl values callee foundShape lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          esl H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl _ _ (fun hn => absurd hn hvn),H',hH',hret _ _ _ _ _ _ pre rr⟩,
                (fun v e => by cases e),by simp,by simp⟩)
            | exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqgd_callSpecS
#print axioms aqgd_callAssignFS
end gen

section wr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}

theorem pxr_of_dapost {H1 : BitVec 64} {M M' : Mem} {G' : GA} (hJE : ∀ x, InJ J C x → Excl x)
    (hSE : ∀ x, SkWin SKB x → Excl x) (h01 : H0.toNat ≤ H1.toNat) (fr : ∀ x, Out x → ¬ Excl x → M x = M0 x)
    (post : DAPost n c T Out ko D B J C SKB H1 M M' G') : PXR n c T Out ko D B Excl H0 M0 M' G' := by
  obtain ⟨H',hH2,hle,reg',⟨Nj',hn'⟩,fr'⟩ := post
  exact ⟨H',Nj',hH2,le_trans h01 hle,reg',hn',
    fun x ho hx => (fr' x ho (fun j => hx (hJE x j)) (fun k => hx (hSE x k))).trans (fr x ho hx)⟩

set_option maxHeartbeats 16000000 in
/-- The actual `increment_nonce(sender)` call keeping `PXR` (journal and key-buffer writes inside `Excl`). -/
theorem aqgd_call_incNonce {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hx : ∀ L, LP L → ∃ X : BitVec 64, L.lookup (ofString "sender") = some (.val (.word X))) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "increment_nonce") [.var .local (ofString "sender")]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsb (incrementNonceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (hkoWs M0')) (keepsBo_of_installed originalRuntimeCode_incrementNonce_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ ⟨lp,_⟩ _ args lookup
    obtain ⟨X,hX⟩ := hx _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hX] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨X,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

set_option maxHeartbeats 16000000 in
/-- The actual `set_account_balance(sender, bal)` call keeping `PXR`. -/
theorem aqgd_call_setBal {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "set_account_balance")
        [.var .local (ofString "sender"),.var .local (ofString "bal")]) := by
  refine aqgd_callSpecS (Vn' := fun x => x ≠ ofString "amount")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_setAccountBalance_lookup (fun _ _ _ h => (setBal_callee h).1) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsb (setAccountBalanceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (hkoWs M0')) (keepsBo_of_installed originalRuntimeCode_setAccountBalance_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨⟨(setBal_callee lookup).2.2,(setBal_callee lookup).2.1⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

/-- `bal = u256_sub(bal, x)`: a result-assigning read-only call keeping `LPS`. -/
theorem aqgd_u256Sub_lps {Ix : BitVec 64} {X : Mem → GA → Prop} {A : GA → Prop} (args : List (ExpHOL 64)) :
    AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun L M G => LPS Ix L ∧ X M G) RR
      (.call (some (some (.local,ofString "bal"),none)) (ofString "u256_sub") args) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun L M G v M' G' pre ⟨e1,e2⟩ => by rw [e1,e2]; exact ⟨lps_upd pre.1 _ v (by decide) (by decide),pre.2⟩)

#print axioms aqgd_call_incNonce
#print axioms aqgd_call_setBal
#print axioms aqgd_u256Sub_lps
end wr

section pw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- The actual `process_transaction` body from the `increment_nonce(sender)` call through the sender balance
debit (`bal = u256_sub(...)` twice, `set_account_balance(sender, bal)`) to the `te_new()` declaration: every path
keeps `PXR` with the journal and key-buffer windows inside `Excl`. No callee frame hypotheses. -/
theorem processTx_writers_aqgd {QM : Mem → GA → Prop} (Ix : BitVec 64) (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hrest : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 28 (sourceFunctionBody Guest.guestFn_process_transaction)) := by
  unfold sourceFunctionBody at hrest ⊢
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq] at hrest ⊢
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop] at hrest ⊢
  refine aqgd_seq (aqgd_call_incNonce ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE (fun _ lp => lp.2)) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_u256Sub_lps _) ?_
  refine aqgd_seq (aqgd_u256Sub_lps _) ?_
  refine aqgd_seq (aqgd_call_setBal ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE) ?_
  refine aqgd_seq aqgd_skip ?_
  exact hrest

#print axioms processTx_writers_aqgd
/-- The actual `process_transaction` body from `bal_index = index + 1` (just after `state_fresh_tx()`) to the
`te_new()` declaration, composed from `processTx_prefix_aqgd` and `processTx_writers_aqgd`. Remaining temporary
scoped callee premises: `FrameC` for `encode_transaction`, `recover_sender_with_chain_id`, `check_transaction`,
`calculate_blob_gas_price`. -/
theorem processTx_to_teNew_aqgd {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    (fcEnc : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction))
    (fcRec : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
    (fcChk : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction))
    (fcBgp : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
    (hBoD : D (Bo + 24)) (hBoO : Out (Bo + 24)) (hBoE : ¬ Excl (Bo + 24)) (hArr : M0 (Bo + 24) = .word Arr)
    (hO0 : Out (Arr + Ix * 16) ∧ ∀ i, Arr + Ix * 16 ≠ c i) (hE0 : Excl (Arr + Ix * 16)) (hw0 : w ≠ Arr + Ix * 16)
    (hO8 : Out (Arr + Ix * 16 + 8) ∧ ∀ i, Arr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Arr + Ix * 16 + 8))
    (hw8 : w ≠ Arr + Ix * 16 + 8)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hrest : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_prefix_aqgd Ix Arr fcEnc fcRec fcChk fcBgp hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8 hw8 hAB hAo hBo hTs hBs
    hcA hcB hOut hwP p0 K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs
    (processTx_writers_aqgd Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hrest)

#print axioms processTx_to_teNew_aqgd
end pw
end InitECandidate.Runtime
