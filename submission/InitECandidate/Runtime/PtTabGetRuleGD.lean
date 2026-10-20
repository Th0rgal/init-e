import InitECandidate.Runtime.PtTabSetRuleGD
import InitECandidate.Runtime.HashGetValueProperty
import InitECandidate.Runtime.HtabReadOnly
/-!
The actual `var {1,1} m = htab_get(t, k)` on a block-object table with a values invariant (`TabRV`): the call is
read-only (`htabGet_memoryFrame`) and a returned pair `(present, value)` has `present ∈ {0, 1}` and `value ∈ S` when
`present ≠ 0` (root's body-level value property on the clock-lifted run).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cs
variable {D : BitVec 64 → Prop} {B : Bool} {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64}
  {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

/-- A declared call against a callee spec; the entry premise also sees the memory domain. -/
theorem aqgd_decCallSpecD {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop} {Vn' : MlS → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals → s.memaddrs = D →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQGD D B A w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQGD D B A w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
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
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw dom.2.1 H hH pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                obtain ⟨H',hH',rr⟩ := r1 v rfl
                have pc := hret _ _ _ _ _ _ pre rr ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by obtain ⟨d1,d2,d3⟩ := dom; exact ⟨fun a ha => d1 a (meta'.2.1 ▸ ha),meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩)
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx H' (by exact hH') pc
                refine ⟨m2.trans m1,a2,fun e => ?_,r2,c2,b2⟩
                obtain ⟨sl2,H2,hH2,q2⟩ := n2 e
                exact ⟨sl_restore sl2 sl name,H2,hH2,hq _ _ _ _ _ _ pre q2⟩
              · exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqgd_decCallSpecD

/-- Strengthen the return predicate with any fact proven about the returned runs. -/
theorem aqgd_addReturn {P Q : GA → Mem → GA → Prop} {X : ValueHOL 64 → Prop} {p : ProgHOL 64}
    (h : AQGD D B A w Vn P Q RR p)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomD D B s → A s.globals →
      SL Vn s.locals → P s.locals s.memory s.globals → ∀ (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState s p = (some (.returned v),post) → X v) :
    AQGD D B A w Vn P Q (fun v M G => RR v M G ∧ X v) p := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl _ rfl pre
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',q⟩ := r v e
  exact ⟨H',hH',q,hr s code dom aw sl pre v _ (Prod.ext e rfl)⟩

#print axioms aqgd_addReturn
end cs

/-- A returned run of the actual `htab_get` body on a `TabRV` table returns `(present, value)` with `present ∈ {0,1}`
and `value ∈ S` when `present ≠ 0`. -/
theorem getRV_ret {F : Type} {D : BitVec 64 → Prop} {B : Bool} (s post : PanSemStateFiniteExact 64 F)
    (T K Hc Hl : BitVec 64) (l : TLay) (S : Set (BitVec 64)) (v : ValueHOL 64)
    (hd : s.memaddrs = D) (hb : s.be = B) (code : s.code = originalRuntimeCode)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) (rv : TabRV D B T l Hl S s.memory)
    (hH : s.globals.lookup (ofString "heap_ptr") = some (.val (.word Hc))) (le : Hl.toNat ≤ Hc.toNat)
    (hHE : Hc.toNat ≤ 33806089496) (al : Hc.toNat % 8 = 0)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (tl : s.locals.lookup (ofString "t") = some (.val (.word T)))
    (kl : s.locals.lookup (ofString "key") = some (.val (.word K)))
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_get) = (some (.returned v),post)) :
    ∃ p val : BitVec 64, v = .rStruct [.val (.word p),.val (.word val)] ∧ (p = 0 ∨ p = 1) ∧ (p ≠ 0 → val ∈ S) := by
  obtain ⟨F0,s0,P,hm,hd0,hb0,hc0,hP,_,_,rd,vi⟩ := rv
  let s' : PanSemStateFiniteExact 64 F := liftClock s (2 ^ 74)
  have rd' := rd.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm) (code.trans hc0.symm) hH
    (by have := rd.live.frontier.allocated; omega) hHE al
  have vi' := vi.transferX (r := s') hm.symm (hd.trans hd0.symm) (hb.trans hb0.symm)
  have lift := panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_htab_get) s _ post (2 ^ 74) ⟨run,by simp⟩
  have lift' : evaluateHOLFiniteState s' (sourceFunctionBody Guest.guestFn_htab_get) =
      (some (.returned v),liftClock post (2 ^ 74)) := lift
  have eK : ∀ o : Nat, o < 52 → (K + BitVec.ofNat 64 o).toNat = K.toNat + o := fun o ho => by
    rw [BitVec.toNat_add]; simp; omega
  have klen : l.KL.toNat ≤ 52 := by rcases sup with h | h | h <;> simp [h]
  have hcap : l.C.toNat * 16 < 2 ^ 64 := by have := rd.live.arrays.endBound; omega
  obtain ⟨p,val,post2,bool,run2,_,_,_,_,_,_,_,prop⟩ := evaluate_source_hashGet_supported_value_property s' l.KL T l.KS
    l.SD l.C l.US l.VS l.OS l.OPS l.N K l.b (fun x => x ∈ S) sup rd'.live.arrays tl kl hK
    (fun o ho => by show s.memaddrs _; rw [hd]; exact Dall _ (by rw [eK o (by omega)]; omega))
    (fun o ho => by
      show s.memaddrs _; rw [hd]; refine Dall _ ?_
      rw [panByteAlign_toNat64,eK o (by omega)]
      have := Nat.div_mul_le_self (K.toNat + o) 8; omega)
    (vi' l.C l.US l.VS rd'.live.arrays.cell16 rd'.live.arrays.cell48 rd'.live.arrays.cell40)
    (by show 2 * l.C.toNat + 2 ≤ s.clock + 2 ^ 74; omega)
  rw [lift'] at run2
  simp only [Prod.mk.injEq,Option.some.injEq,PanSemResultExact.returned.injEq] at run2
  exact ⟨p,val,run2.1,bool,prop⟩

#print axioms getRV_ret

section tg
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var {1,1} name = htab_get(t, k)` on a `TabRV` table: read-only, and the continuation starts from the
call-site state with `name = (present, value)`, `present ∈ {0,1}`, `value ∈ S` when `present ≠ 0`. -/
theorem aqgd_decCall_htabGet_rv {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (et ek : ExpHOL 64)
    {cont : ProgHOL 64} (T K Hl Hc : BitVec 64) (l : TLay) (S : Set (BitVec 64)) (M1 : Mem) (G1 : GA)
    (rv : TabRV D B T l Hl S M1) (hH1 : HeapIs G1 Hc) (hHl : Hl.toNat ≤ Hc.toNat)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (sup : l.KL = 20 ∨ l.KL = 32 ∨ l.KL = 52) (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ek] =
        some [.val (.word T),.val (.word K)])
    (hshape : Vn name → ShapeHOL.comb [.one,.one] = .one)
    (hres : ∀ (L : GA) (p val : BitVec 64), LP L → (p = 0 ∨ p = 1) → (p ≠ 0 → val ∈ S) →
      Pc (L.update (name,.rStruct [.val (.word p),.val (.word val)])) M1 G1)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name (.comb [.one,.one]) (ofString "htab_get") [et,ek] cont) := by
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "t") = some (.val (.word T)) ∧
      L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' v M' G' => (M' = M0' ∧ G' = G0') ∧ ∃ p val : BitVec 64,
      v = .rStruct [.val (.word p),.val (.word val)] ∧ (p = 0 ∨ p = 1) ∧ (p ≠ 0 → val ∈ S))
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp) ?_ ?_ hshape ?_ hc ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    refine aqgd_addReturn (aqgd_conseq (aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0') (fun _ _ _ h => h.2) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)) ?_
    intro F s code dom aw _ ⟨⟨tl,kl⟩,sm,sg⟩ v post run
    have hH : HeapIs s.globals Hc := by rw [sg,hG]; exact hH1
    have hf := jws_heap_facts aw.1.1.1 hH
    exact getRV_ret s post T K Hc Hl l S v dom.2.1 dom.2.2 code Dall (by rw [sm,hM]; exact rv) hH hHl hf.2.1 hf.2.2
      sup hK hKE tl kl run
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup_shape _ _ (ofString "t") (ofString "key") _ _ _ _ (by decide)
      originalRuntimeCode_hashGet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨⟨eM,eG⟩,p,val,ev,bool,prop⟩ _
    rw [eM,eG,hM,hG,ev]
    exact hres L p val lp bool prop
  · intro L M G L' M' G' ⟨lp,_,_⟩ qc
    exact hq L L' M' G' lp qc

#print axioms aqgd_decCall_htabGet_rv
end tg
end InitECandidate.Runtime
