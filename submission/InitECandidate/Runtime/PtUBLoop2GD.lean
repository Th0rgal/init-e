import InitECandidate.Runtime.PtUBItemLoopGD
/-!
The storage loop of `update_builder_from_tx` (`ubLoop2`) in the builder world: for each live item of the storage outer
map `outer` (an address with its inner table), the inner loop over the inner table's items with the storage item body.
The inner tables' content (from the source-table validity at the builder entry) and regions are explicit premises.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The count cell of a content table. -/
theorem tcont_cell24 {D : BitVec 64 → Prop} {B : Bool} {M : Mem} {Tt : BitVec 64} {l : TLay} (tc : TCont D B M Tt l) :
    M (Tt + 24#64) = .word l.N ∧ D (Tt + 24#64) := by
  obtain ⟨F,s,hm,hd,_,_,inv,_⟩ := tc
  have ta := inv.tableAligned; have hk := inv.headerKeys; have k1 := inv.keysBefore; have k3 := inv.usedBefore
  have k4 := inv.orderBefore; have k5 := inv.endBound
  have e : (Tt + 24#64).toNat = Tt.toNat + 24 := by rw [BitVec.toNat_add]; simp; omega
  have d1 : (Tt + 24#64).toNat % 8 = 0 := by rw [e]; omega
  have d2 : Tt.toNat ≤ (Tt + 24#64).toNat := by rw [e]; omega
  have d3 : (Tt + 24#64).toNat < l.OPS.toNat + l.C.toNat * 8 := by rw [e]; omega
  exact ⟨by rw [← hm]; exact inv.cell24,by rw [← hd]; exact inv.domain _ d1 d2 d3⟩

/-- A cell of the order or values array of a content table lies in its region. -/
theorem tcont_cells_in {D : BitVec 64 → Prop} {B : Bool} {M : Mem} {Tt : BitVec 64} {l : TLay} (tc : TCont D B M Tt l)
    (I slot : BitVec 64) (hI : I.toNat < l.C.toNat) (hs : slot.toNat < l.C.toNat) :
    InTabF Tt l.KS l.SD l.C l.US l.VS l.OS l.OPS (l.OS + I * 8) ∧
      InTabF Tt l.KS l.SD l.C l.US l.VS l.OS l.OPS (l.VS + slot * 8) := by
  obtain ⟨F,s,_,_,_,_,inv,_⟩ := tc
  have k1 := inv.keysBefore; have k2 := inv.valuesBefore; have k3 := inv.usedBefore; have k4 := inv.orderBefore
  have k5 := inv.endBound
  have e1 : (l.OS + I * 8).toNat = l.OS.toNat + I.toNat * 8 := itm_toNat_add_mul8 _ _ (by omega)
  have e2 : (l.VS + slot * 8).toNat = l.VS.toNat + slot.toNat * 8 := itm_toNat_add_mul8 _ _ (by omega)
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [e1]; omega,by rw [e1]; omega⟩)))),
    Or.inr (Or.inr (Or.inl ⟨by rw [e2]; omega,by rw [e2]; omega⟩))⟩

theorem ubInnerLoop_eq : ubInnerLoop = itemLoopP (ofString "j") (ofString "icap") (ofString "inner") (ofString "e")
    ubStorThen := rfl

theorem ubLoop2_eq : ubLoop2 = itemLoopP (ofString "i") (ofString "cap") (ofString "outer") (ofString "s2")
    ubOuterThen := rfl

section l2
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}
  {ADs0 : Set (BitVec 64)} {Rg0 : BalK → BitVec 64 → Prop} {H0 : BitVec 64} {Rr0 Ow0 : BitVec 64 → Prop} {M0 : Mem}

/-- Outside every region the builder writes, below the entry heap. -/
def UOut (ADs0 : Set (BitVec 64)) (Rg0 : BalK → BitVec 64 → Prop) (H0 : BitVec 64) (Rr0 Ow0 : BitVec 64 → Prop)
    (x : BitVec 64) : Prop :=
  x.toNat < H0.toNat ∧ (∀ k, BalK.live ADs0 k → ¬ Rg0 k x) ∧ ¬ Rr0 x ∧ ¬ Ow0 x

theorem ubOuterThen_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (Iv Tout : BitVec 64) (lout : TLay)
    (hOutR : ∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (hIn : ∀ I slot vv : BitVec 64, I.toNat < lout.N.toNat → M0 (lout.OS + I * 8) = .word slot →
      M0 (lout.VS + slot * 8) = .word vv → ∃ li : TLay, (TCont D B M0 vv li ∧ 20 ≤ li.KL.toNat ∧
        li.N.toNat < li.C.toNat) ∧ ∀ x, InTabF vv li.KS li.SD li.C li.US li.VS li.OS li.OPS x →
          UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (I b A Vin slot : BitVec 64) (hI : I.toNat < lout.N.toNat) (hA : A.toNat % 8 = 0)
    (hAE : A.toNat + 52 ≤ 33806089496) (hsl : slot.toNat < lout.C.toNat) (ncO : lout.N.toNat < lout.C.toNat)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (tcO : TCont D B M0 Tout lout) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (((LK ((ofString "i",I) :: [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)]) L ∧
        True) ∧ L.lookup (ofString "s2") = some (.rStruct [.val (.word b),.val (.word A),.val (.word Vin)])) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        (M (lout.OS + I * 8) = .word slot ∧ M (lout.VS + slot * 8) = .word Vin))
      (fun L M G => (LK ((ofString "i",I) :: [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)]) L ∧
        True) ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G)
      (fun _ _ _ => False) ubOuterThen := by
  let po : List (MlS × BitVec 64) :=
    (ofString "i",I) :: [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)]
  let W := fun M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G
  have pne : ∀ (x : MlS), x ≠ ofString "i" → x ≠ ofString "idx" → x ≠ ofString "outer" → x ≠ ofString "cap" →
      ∀ p ∈ po, p.1 ≠ x := by
    intro x h1 h2 h3 h4 p hp
    simp only [po,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    exacts [h1.symm,h2.symm,h3.symm,h4.symm]
  -- the inner table at the entry memory
  refine aqgd_conseq (P := fun L M G => ((LK po L ∧ L.lookup (ofString "s2") =
      some (.rStruct [.val (.word b),.val (.word A),.val (.word Vin)])) ∧ (W M G ∧
      (M (lout.OS + I * 8) = .word slot ∧ M (lout.VS + slot * 8) = .word Vin))))
    (aqgd_ghostR (fun M1 G1 ⟨st,c1,c2⟩ => ?_)) (fun L M G ⟨⟨⟨⟨lk,_⟩,l2⟩,st⟩,cc⟩ => ⟨⟨lk,l2⟩,st,cc⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  obtain ⟨cO,cV⟩ := tcont_cells_in tcO I slot (by omega) hsl
  have fr0 : ∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → M1 x = M0 x := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fr⟩ := st
    exact fun x hx => let ⟨a,b',c',d⟩ := hOutR x hx; fr x a b' c' d
  obtain ⟨li,⟨tci,kli,nci⟩,hiR⟩ := hIn I slot Vin hI (by rw [← fr0 _ cO]; exact c1) (by rw [← fr0 _ cV]; exact c2)
  have hTCi : ∀ M G, W M G → TCont D B M Vin li := fun M G st' => tcont_of_ust tci nci.le hiR st'
  obtain ⟨cell,dom24⟩ := tcont_cell24 (hTCi M1 G1 st)
  unfold ubOuterThen
  let Qo : GA → Mem → GA → Prop := fun L M G => (LK po L ∧ True) ∧ W M G
  -- inner = s2.2; icap = lds (inner + 24); j = 0
  refine aqgd_decD (Pb := fun L M G => ((LK ((ofString "inner",Vin) :: po) L ∧ L.lookup (ofString "s2") =
      some (.rStruct [.val (.word b),.val (.word A),.val (.word Vin)])) ∧ M = M1 ∧ G = G1)) (Qb := Qo)
    _ _ _ (fun h => h.elim) ?_ ?_ (fun L M G L' M' G' _ ⟨⟨lk,_⟩,st'⟩ =>
      ⟨⟨lk_resVar lk _ _ (pne _ (by decide) (by decide) (by decide) (by decide)),trivial⟩,st'⟩)
  · intro F s v _ _ _ _ ⟨⟨lk,l2⟩,hM,hG⟩ _ ev _
    simp [EV,evalHOLExact,l2] at ev; subst ev
    refine ⟨⟨fun p hp => ?_,by rw [lookup_update_ne' _ _ (by decide)]; exact l2⟩,hM,hG⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact lookup_update_eq' _ _ _
    · rw [lookup_update_ne' _ _ (pne _ (by decide) (by decide) (by decide) (by decide) p hp)]; exact lk p hp
  refine aqgd_decD (Pb := fun L M G => ((LK ((ofString "icap",li.N) :: (ofString "inner",Vin) :: po) L ∧
      L.lookup (ofString "s2") = some (.rStruct [.val (.word b),.val (.word A),.val (.word Vin)])) ∧
      M = M1 ∧ G = G1)) (Qb := fun L M G => ((LK ((ofString "inner",Vin) :: po) L ∧ True) ∧ W M G))
    _ _ _ (fun h => h.elim) ?_ ?_ (fun L M G L' M' G' _ ⟨⟨lk,_⟩,st'⟩ =>
      ⟨⟨lk_resVar (lk_tail lk) _ _ (pne _ (by decide) (by decide) (by decide) (by decide)),trivial⟩,st'⟩)
  · intro F s v _ _ dom _ ⟨⟨lk,l2⟩,hM,hG⟩ _ ev _
    unfold EV at ev
    rw [eval_record_word s .local (ofString "inner") Vin 24#64 li.N
      (by simp [evalHOLExact,lk_get lk _ _ (List.mem_cons_self)]) (by rw [dom.2.1]; exact dom24)
      (by rw [hM]; exact cell)] at ev
    simp only [Option.some.injEq] at ev; subst ev
    refine ⟨⟨fun p hp => ?_,by rw [lookup_update_ne' _ _ (by decide)]; exact l2⟩,hM,hG⟩
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact lookup_update_eq' _ _ _
    · rw [lookup_update_ne' _ _ (show ofString "inner" ≠ ofString "icap" by decide)]; exact lk_get lk _ _ (List.mem_cons_self)
    · rw [lookup_update_ne' _ _ (pne _ (by decide) (by decide) (by decide) (by decide) p hp)]
      exact lk p (List.mem_cons_of_mem _ hp)
  let pin : List (MlS × BitVec 64) := (ofString "icap",li.N) :: (ofString "inner",Vin) :: po
  let X : GA → Prop := fun L => L.lookup (ofString "s2") = some (.rStruct [.val (.word b),.val (.word A),.val (.word Vin)])
  have pinne : ∀ (x : MlS), x ≠ ofString "icap" → x ≠ ofString "inner" → x ≠ ofString "i" → x ≠ ofString "idx" →
      x ≠ ofString "outer" → x ≠ ofString "cap" → ∀ p ∈ pin, p.1 ≠ x := by
    intro x h0 h1 h2 h3 h4 h5 p hp
    simp only [pin,po,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm,h1.symm,h2.symm,h3.symm,h4.symm,h5.symm]
  refine aqgd_decD (Pb := fun L M G => ((LK pin L ∧ X L) ∧ W M G) ∧
      ∃ J' : BitVec 64, L.lookup (ofString "j") = some (.val (.word J')) ∧ J'.toNat ≤ li.N.toNat)
    (Qb := fun L M G => ((LK pin L ∧ X L) ∧ W M G) ∧
      ∃ J' : BitVec 64, L.lookup (ofString "j") = some (.val (.word J')) ∧ J'.toNat ≤ li.N.toNat)
    _ _ _ (fun h => h.elim) ?_ ?_ (fun L M G L' M' G' _ ⟨⟨⟨lk,_⟩,st'⟩,_⟩ =>
      ⟨⟨lk_resVar (lk_tail lk) _ _ (by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · show ofString "inner" ≠ ofString "j"; decide
        · exact pne _ (by decide) (by decide) (by decide) (by decide) p hp),trivial⟩,st'⟩)
  · intro F s v _ _ _ _ ⟨⟨lk,l2⟩,hM,hG⟩ _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨⟨⟨lk_update lk _ _ (pinne _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
      by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact l2⟩,by rw [hM,hG]; exact st⟩,
      0#64,lookup_update_eq' _ _ _,by simp⟩
  rw [ubInnerLoop_eq]
  refine itemLoop_aqgd (ofString "j") (ofString "icap") (ofString "inner") (ofString "e") ubStorThen pin X W Vin li hTCi
    kli nci (by simp [pin]) (by simp [pin]) (pinne _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (pinne _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)
    (fun L v lx => ⟨by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact lx,
      by show _ = _; rw [lookup_update_ne' _ _ (by decide)]; exact lx⟩)
    (fun L o lx => by show _ = _; rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact lx) ?_
  intro J' be Kk Pv slot' _ hK8 hK52 _
  have hpn : ∀ p ∈ (ofString "j",J') :: pin, p.1 ∉ storNames := by
    intro p hp
    simp only [pin,po,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  exact aqgd_conseq (ubStorThen_aqgd bk wsr ne Bs hBs hcB ((ofString "j",J') :: pin) hpn Iv (by simp [pin,po]) b A Vin
      be Kk Pv hA hAE hK8 hK52 hwP hw0 hwk0 hwR0 hwO0 Dall)
    (fun L M G ⟨⟨⟨⟨lk,lx⟩,le⟩,hw⟩,_⟩ => ⟨⟨⟨lk,lx⟩,le⟩,hw⟩) (fun L M G ⟨⟨lk,lx⟩,hw⟩ => ⟨⟨lk,lx⟩,hw⟩)
    (fun _ _ _ h => h)

#print axioms ubOuterThen_aqgd

/-- The storage loop. -/
theorem ubLoop2_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (Iv Tout : BitVec 64) (lout : TLay) (tcO : TCont D B M0 Tout lout)
    (klO : 20 ≤ lout.KL.toNat) (ncO : lout.N.toNat < lout.C.toNat)
    (hOutR : ∀ x, InTabF Tout lout.KS lout.SD lout.C lout.US lout.VS lout.OS lout.OPS x → UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (hIn : ∀ I slot vv : BitVec 64, I.toNat < lout.N.toNat → M0 (lout.OS + I * 8) = .word slot →
      M0 (lout.VS + slot * 8) = .word vv → ∃ li : TLay, (TCont D B M0 vv li ∧ 20 ≤ li.KL.toNat ∧
        li.N.toNat < li.C.toNat) ∧ ∀ x, InTabF vv li.KS li.SD li.C li.US li.VS li.OS li.OPS x →
          UOut ADs0 Rg0 H0 Rr0 Ow0 x)
    (hwP : w.toNat < P0.toNat) (hw0 : w.toNat < H0.toNat) (hwk0 : ∀ k, BalK.live ADs0 k → ¬ Rg0 k w)
    (hwR0 : ¬ Rr0 w) (hwO0 : ¬ Ow0 w) (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LK [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)] L ∧ True) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ lout.N.toNat)
      (fun L M G => ((LK [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)] L ∧ True) ∧
        USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs0 Rg0 H0 Rr0 Ow0 M0 M G) ∧
        ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ lout.N.toNat)
      (fun _ _ _ => False) ubLoop2 := by
  rw [ubLoop2_eq]
  have pne : ∀ (x : MlS), x ≠ ofString "idx" → x ≠ ofString "outer" → x ≠ ofString "cap" →
      ∀ p ∈ [(ofString "idx",Iv),(ofString "outer",Tout),(ofString "cap",lout.N)], p.1 ≠ x := by
    intro x h1 h2 h3 p hp
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl
    exacts [h1.symm,h2.symm,h3.symm]
  exact itemLoop_aqgd (ofString "i") (ofString "cap") (ofString "outer") (ofString "s2") ubOuterThen _ (fun _ => True)
    _ Tout lout (fun M G st => tcont_of_ust tcO ncO.le hOutR st) klO ncO (by simp) (by simp)
    (pne _ (by decide) (by decide) (by decide)) (pne _ (by decide) (by decide) (by decide)) (by decide)
    (fun _ _ _ => ⟨trivial,trivial⟩) (fun _ _ _ => trivial)
    (fun I b A Vin slot hI hA8 hA52 hsl => ubOuterThen_aqgd bk wsr ne Bs hBs hcB Iv Tout lout hOutR hIn I b A Vin slot
      hI hA8 hA52 hsl ncO hwP hw0 hwk0 hwR0 hwO0 Dall tcO)

#print axioms ubLoop2_aqgd
end l2
end InitECandidate.Runtime
