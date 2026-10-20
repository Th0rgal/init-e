import InitECandidate.Runtime.PtIdxStorGD
/-!
World-level statements of the block-access-list builder: the six writer call statements and the two index-start
declared calls are world steps (`USt`) from the call entry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section wr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Nj : BitVec 64}
  {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop}
  {M2 : Mem} {G2 : GA}

/-- The world-level `add_balance_change` call statement. -/
theorem aqgd_call_addBalanceW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea ei eb : ExpHOL 64)
    (A I b0 b1 b2 b3 : BitVec 64) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,eb] =
        some [.val (.word A),.val (.word I),.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "add_balance_change") [ea,ei,eb]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_addBalance bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A I b0 b1 b2 b3 hwP p0 hK hKE Dall (LP := LP) _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_addBalanceW

/-- The world-level `add_nonce_change` call statement. -/
theorem aqgd_call_addNonceW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea ei en : ExpHOL 64)
    (A I Nn : BitVec 64) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,en] =
        some [.val (.word A),.val (.word I),.val (.word Nn)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "add_nonce_change") [ea,ei,en]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_addNonce bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A I Nn hwP p0 hK hKE Dall (LP := LP) _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_addNonceW

/-- The world-level `add_code_change` call statement. -/
theorem aqgd_call_addCodeW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea ei ec el : ExpHOL 64)
    (A I Cd Cl : BitVec 64) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ei,ec,el] =
        some [.val (.word A),.val (.word I),.val (.word Cd),.val (.word Cl)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "add_code_change") [ea,ei,ec,el]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_addCode bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A I Cd Cl hwP p0 hK hKE Dall (LP := LP) _ _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_addCodeW

/-- The world-level `add_storage_write` call statement. -/
theorem aqgd_call_addStorageW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea es ei ev : ExpHOL 64)
    (A Sl I v0 v1 v2 v3 : BitVec 64) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,es,ei,ev] =
        some [.val (.word A),.val (.word Sl),.val (.word I),.rStruct [.val (.word v0),.val (.word v1),.val (.word v2),.val (.word v3)]]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "add_storage_write") [ea,es,ei,ev]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_call_addStorage bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A Sl I v0 v1 v2 v3 hwP p0 hK hKE hS hSE Dall (LP := LP) _ _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_addStorageW

/-- The world-level `bal_remove_change` call statement. -/
theorem aqgd_call_removeChangeW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea ew ee ei : ExpHOL 64)
    (A Wc E I : BitVec 64) (sel : ChgSel Wc E) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ew,ee,ei] =
        some [.val (.word A),.val (.word Wc),.val (.word E),.val (.word I)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "bal_remove_change") [ea,ew,ee,ei]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,show goodGA (ofString "bal_remove_change") = true by decide])
      (aqgd_call_removeChange bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A Wc E I sel hK hKE Dall (LP := LP) _ _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_removeChangeW

/-- The world-level `remove_storage_write` call statement. -/
theorem aqgd_call_removeStorageW (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} (ea es ei : ExpHOL 64)
    (A Sl I : BitVec 64) (hK : A.toNat % 8 = 0) (hKE : A.toNat + 52 ≤ 33806089496)
    (hS : Sl.toNat % 8 = 0) (hSE : Sl.toNat + 52 ≤ 33806089496)
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w)
    (Dall : ∀ a : BitVec 64, a.toNat < 33806089496 → D a)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M2 → s.globals = G2 → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,es,ei] =
        some [.val (.word A),.val (.word Sl),.val (.word I)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "remove_storage_write") [ea,es,ei]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,show goodGA (ofString "remove_storage_write") = true by decide])
      (aqgd_call_removeStorage bk BA IA IS KB Ix ADs Rg H Nj M2 G2 bw hH hn bg hwk A Sl I hK hKE hS hSE Dall (LP := LP) _ _ _ hargs))
    (fun L M G h => ⟨h,by rw [h.2.2]; exact bg⟩) (fun L M G ⟨⟨lp,bs⟩,bg'⟩ => ⟨lp,ust_of_balStep wsf u bs bg'⟩)
    (fun _ _ _ h => h.1)

#print axioms aqgd_call_removeStorageW

/-- The world-level declared call `name = idx_start_account(ea)`. -/
theorem aqgd_decCall_isaW (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ea : ExpHOL 64)
    {cont : ProgHOL 64} (A : BitVec 64) (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M2 → s.globals = G2 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea] =
        some [.val (.word A)])
    (hres : ∀ (L : GA) (y : BitVec 64) (M : Mem) (G : GA), LP L →
      USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G → Pc (L.update (name,.val (.word y))) M G)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2) Q RR
      (.decCall name .one (ofString "idx_start_account") [ea] cont) := by
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ v M' G' => (∃ y : BitVec 64, v = .val (.word y)) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M' G')
    _ _ _ _ _ _ _ originalRuntimeCode_idxStartAccount_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact aqgd_conseq (idxStartAcct_aqgd bk wsr ne Bs hBs hcB A u hwP hwk hwR hwO) (fun _ _ _ h => h)
        (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ hc
    (fun L _ _ L' M' G' ⟨lp,_,_⟩ q => hq L L' M' G' lp q)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG2⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG2 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_idxStartAccount_lookup lookup
    exact ⟨by rw [e]; simp (config := {decide := true}),rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ ⟨⟨y,hv⟩,st⟩ _
    subst hv
    exact hres L y M' G' lp st

#print axioms aqgd_decCall_isaW

/-- The world-level declared call `name = idx_start_storage(ea, ek)`. -/
theorem aqgd_decCall_issW (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ea ek : ExpHOL 64)
    {cont : ProgHOL 64} (A K : BitVec 64) (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M2 → s.globals = G2 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ek] =
        some [.val (.word A),.val (.word K)])
    (hres : ∀ (L : GA) (a b c' d : BitVec 64) (M : Mem) (G : GA), LP L →
      USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G →
      Pc (L.update (name,.rStruct [.val (.word a),.val (.word b),.val (.word c'),.val (.word d)])) M G)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2) Q RR
      (.decCall name (.comb [.one,.one,.one,.one]) (ofString "idx_start_storage") [ea,ek] cont) := by
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ _ M' G' => USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M' G')
    _ _ _ _ _ _ _ originalRuntimeCode_idxStartStorage_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact aqgd_conseq (idxStartStor_aqgd bk wsr ne Bs hBs hcB A K u hwP hwk hwR hwO) (fun _ _ _ h => h)
        (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ hc
    (fun L _ _ L' M' G' ⟨lp,_,_⟩ q => hq L L' M' G' lp q)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG2⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG2 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_idxStartStorage_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ st sh
    obtain ⟨a,b,c',d,rfl⟩ := shape4r sh
    exact hres L a b c' d M' G' lp st

#print axioms aqgd_decCall_issW
end wr
end InitECandidate.Runtime
