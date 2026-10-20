import InitECandidate.Runtime.PtUBChgGD
/-!
The account item body of `update_builder_from_tx` (`ubAcctThen`) in the builder world: the item fields, the
index-start record (world-level `idx_start_account`), the pre-state/post-state value locals, the reload and the change
decisions.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Names declared by the account item. -/
def itemNames : List MlS :=
  [ofString "addr",ofString "post",ofString "pre",ofString "pre_bal",ofString "pre_nonce",ofString "pre_ch",
    ofString "post_bal",ofString "post_nonce",ofString "post_ch",ofString "eq",ofString "code"]

section it
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}

theorem ubAcctThen_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (pairs : List (MlS × BitVec 64)) (hpn : ∀ p ∈ pairs, p.1 ∉ itemNames) (Iv : BitVec 64)
    (hidx : (ofString "idx",Iv) ∈ pairs) (b K P : BitVec 64)
    (hK : K.toNat % 8 = 0) (hKE : K.toNat + 52 ≤ 33806089496)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LK pairs L ∧ L.lookup (ofString "s") =
        some (.rStruct [.val (.word b),.val (.word K),.val (.word P)])) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun L M G => LK pairs L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun _ _ _ => False) ubAcctThen := by
  have hne : ∀ x ∈ itemNames, ∀ p ∈ pairs, p.1 ≠ x := fun x hx p hp e => hpn p hp (e ▸ hx)
  let W := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G
  let Qo : GA → Mem → GA → Prop := fun L M G => LK pairs L ∧ W M G
  have rq : ∀ (x : MlS), x ∈ itemNames → ∀ (L : GA) (M : Mem) (G : GA) (L' : GA) (M' : Mem) (G' : GA),
      Qo L' M' G' → Qo (L'.resVarEq (x,L.lookup x)) M' G' := fun x hx _ _ _ _ _ _ ⟨lk,st⟩ =>
    ⟨lk_resVar lk _ _ (hne x hx),st⟩
  unfold ubAcctThen
  -- addr = s.1; post = s.2
  refine aqgd_decD (Pb := fun L M G => ((LK pairs L ∧ L.lookup (ofString "addr") = some (.val (.word K))) ∧
      L.lookup (ofString "s") = some (.rStruct [.val (.word b),.val (.word K),.val (.word P)])) ∧ W M G) (Qb := Qo)
    _ _ _ (fun h => h.elim) ?_ ?_ (fun L M G L' M' G' _ q => rq _ (by simp [itemNames]) L M G L' M' G' q)
  · intro F s v _ _ _ _ ⟨⟨lk,ls⟩,hw⟩ _ ev _
    simp [EV,evalHOLExact,ls] at ev; subst ev
    exact ⟨⟨⟨lk_update lk _ _ (hne _ (by simp [itemNames])),lookup_update_eq' _ _ _⟩,
      by rw [lookup_update_ne' _ _ (by decide)]; exact ls⟩,hw⟩
  refine aqgd_decD (Pb := fun L M G => ((LK pairs L ∧ L.lookup (ofString "addr") = some (.val (.word K))) ∧
      L.lookup (ofString "post") = some (.val (.word P))) ∧ W M G)
    (Qb := Qo) _ _ _ (fun h => h.elim) ?_ ?_ (fun L M G L' M' G' _ q => rq _ (by simp [itemNames]) L M G L' M' G' q)
  · intro F s v _ _ _ _ ⟨⟨⟨lk,la⟩,ls⟩,hw⟩ _ ev _
    simp [EV,evalHOLExact,ls] at ev; subst ev
    exact ⟨⟨⟨lk_update lk _ _ (hne _ (by simp [itemNames])),by rw [lookup_update_ne' _ _ (by decide)]; exact la⟩,
      lookup_update_eq' _ _ _⟩,hw⟩
  -- pre = idx_start_account(addr) and the rest, from the current world
  refine aqgd_conseq (aqgd_ust (LP' := fun L => LK pairs L) (X := fun _ => False)
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) hw0 hwk0 hwR0 hwO0)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim)
  have hw2 : w.toNat < H2.toNat := by omega
  let W2 := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G
  let Q2 : GA → Mem → GA → Prop := fun L M G => LK pairs L ∧ W2 M G
  have rq2 : ∀ (x : MlS), x ∈ itemNames → ∀ (L : GA) (M : Mem) (G : GA) (L' : GA) (M' : Mem) (G' : GA),
      Q2 L' M' G' → Q2 (L'.resVarEq (x,L.lookup x)) M' G' := fun x hx _ _ _ _ _ _ ⟨lk,st⟩ =>
    ⟨lk_resVar lk _ _ (hne x hx),st⟩
  refine aqgd_decCall_isaW bk wsr ne Bs hBs hcB
    (LP := fun L => (LK pairs L ∧ L.lookup (ofString "addr") = some (.val (.word K))) ∧
      L.lookup (ofString "post") = some (.val (.word P)))
    (Pc := fun L M G => ∃ y : BitVec 64, (((LK pairs L ∧ L.lookup (ofString "addr") = some (.val (.word K))) ∧
      L.lookup (ofString "post") = some (.val (.word P))) ∧ L.lookup (ofString "pre") = some (.val (.word y))) ∧
      W2 M G)
    (Qc := Q2) (ofString "pre") _ K u2 hwP hk2 hr2 ho2 ?_ ?_ ?_
    (fun L L' M' G' _ q => rq2 _ (by simp [itemNames]) L M2 G2 L' M' G' q)
  · intro F s _ _ _ ⟨⟨_,la⟩,_⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la]
  · intro L y M G ⟨⟨lk,la⟩,lp⟩ st
    exact ⟨y,⟨⟨⟨lk_update lk _ _ (hne _ (by simp [itemNames])),by rw [lookup_update_ne' _ _ (by decide)]; exact la⟩,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lp⟩,lookup_update_eq' _ _ _⟩,st⟩
  refine aqgd_ex (fun y => ?_)
  -- the value declarations
  let LA : GA → Prop := fun L => LK pairs L ∧ L.lookup (ofString "addr") = some (.val (.word K))
  have la_upd : ∀ (x : MlS), x ∈ itemNames → ofString "addr" ≠ x → ∀ L v, LA L → LA (L.update (x,v)) :=
    fun x hx hax L v ⟨lk,la⟩ => ⟨lk_update lk _ _ (hne x hx),by rw [lookup_update_ne' _ _ hax]; exact la⟩
  refine aqgd_decD (Pb := fun L M G => LA L ∧ W2 M G) (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ _ ⟨⟨⟨la,_⟩,_⟩,hw⟩ _ _ _ => ⟨la_upd _ (by simp [itemNames]) (by decide) _ _ la,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  refine aqgd_decD (Pb := fun L M G => LA L ∧ W2 M G) (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ _ ⟨la,hw⟩ _ _ _ => ⟨la_upd _ (by simp [itemNames]) (by decide) _ _ la,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  refine aqgd_decD (Pb := fun L M G => LA L ∧ W2 M G) (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ _ ⟨la,hw⟩ _ _ _ => ⟨la_upd _ (by simp [itemNames]) (by decide) _ _ la,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  refine aqgd_decD (Pb := fun L M G => (LA L ∧ L.lookup (ofString "post_bal") =
      some (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)])) ∧ W2 M G)
    (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ _ ⟨la,hw⟩ _ ev _ => by
      simp [EV,evalHOLExact,evalListHOLExact] at ev; subst ev
      exact ⟨⟨la_upd _ (by simp [itemNames]) (by decide) _ _ la,lookup_update_eq' _ _ _⟩,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  refine aqgd_decD (Pb := fun L M G => ((LA L ∧ L.lookup (ofString "post_bal") =
      some (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)])) ∧
      L.lookup (ofString "post_nonce") = some (.val (.word 0#64))) ∧ W2 M G)
    (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ _ _ _ ⟨⟨la,lb⟩,hw⟩ _ ev _ => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨⟨⟨la_upd _ (by simp [itemNames]) (by decide) _ _ la,by rw [lookup_update_ne' _ _ (by decide)]; exact lb⟩,
        lookup_update_eq' _ _ _⟩,hw⟩) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  refine aqgd_decD (Pb := fun L M G => (LK ((ofString "addr",K) :: pairs) L ∧ PVL L) ∧ W2 M G)
    (Qb := Q2) _ _ _ (fun h => h.elim)
    (fun s v _ aw _ _ ⟨⟨⟨la,lb⟩,ln⟩,hw⟩ _ ev _ => by
      obtain ⟨eg,ye,hye⟩ := aw.1.1.1.1.1.2.2.2 (ofString "empty_code_hash") (by decide)
      simp [EV,evalHOLExact,eg,hye] at ev; subst ev
      refine ⟨⟨fun p hp => ?_,⟨0#64,0#64,0#64,0#64,by rw [lookup_update_ne' _ _ (by decide)]; exact lb⟩,
        ⟨0#64,by rw [lookup_update_ne' _ _ (by decide)]; exact ln⟩,⟨ye,lookup_update_eq' _ _ _⟩⟩,hw⟩
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · show (s.locals.update _).lookup (ofString "addr") = _
        rw [lookup_update_ne' _ _ (by decide)]; exact la.2
      · exact lk_update la.1 _ _ (hne _ (by simp [itemNames])) p hp) ?_
    (fun L M G L' M' G' _ q => rq2 _ (by simp [itemNames]) L M G L' M' G' q)
  -- reload and decisions
  have csub : ∀ x, x ∈ chgNames → x ∈ itemNames := by
    intro x hx
    simp only [chgNames,List.mem_cons,List.mem_nil_iff,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  have hpn' : ∀ p ∈ (ofString "addr",K) :: pairs, p.1 ∉ chgNames := fun p hp => by
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · show ofString "addr" ∉ chgNames; decide
    · exact fun h => hpn p hp (csub _ h)
  refine aqgd_seq (ubChgReload_aqgd ((ofString "addr",K) :: pairs) (fun p hp => ⟨fun e => hpn' p hp (by rw [e]; decide),
    fun e => hpn' p hp (by rw [e]; decide),fun e => hpn' p hp (by rw [e]; decide)⟩) W2)
    (aqgd_conseq (ubChgRest_aqgd bk wsr.1 ne40 Ts hTs hc40 hSkSO hSk ((ofString "addr",K) :: pairs) hpn' Iv K
      (List.mem_cons_of_mem _ hidx) List.mem_cons_self hK hKE hwP hw2 hk2 hr2 ho2 Dall)
      (fun _ _ _ h => h) (fun L M G ⟨lk,st⟩ => ⟨fun p hp => lk p (List.mem_cons_of_mem _ hp),st⟩)
      (fun _ _ _ h => h.elim))

#print axioms ubAcctThen_aqgd
end it
end InitECandidate.Runtime
