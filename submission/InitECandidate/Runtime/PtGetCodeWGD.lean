import InitECandidate.Runtime.PtRegSetWGD
/-!
The actual `get_code(code_hash, addr)` in the block-access-list builder world: the read-only lookups (`memeq` with the
empty code hash, the code caches `ts + 48` and `bs + 48`), `sk_make` into the transaction key buffer (scratch region),
`htab_set` on the code-read registry table (`ts + 40`) and the read-only `ws_get_code`; every return is a world step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section gc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop}
  {Sk : BitVec 64 → Prop} {Nj : BitVec 64}

/-- Locals of `get_code`. -/
def GCL (Ch A : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "code_hash") = some (.val (.word Ch)) ∧ L.lookup (ofString "addr") = some (.val (.word A))

theorem gcl_upd {Ch A : BitVec 64} {L : GA} (h : GCL Ch A L) (x : MlS) (v : ValueHOL 64)
    (h1 : ofString "code_hash" ≠ x) (h2 : ofString "addr" ≠ x) : GCL Ch A (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2⟩

/-- A read-only declared call keeps any locals invariant not mentioning the result name. -/
theorem aqgd_roDec {I : GA → Mem → GA → Prop} {Q : GA → Mem → GA → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (returnShape : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hup : ∀ L M G v, I L M G → I (L.update (name,v)) M G)
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) I (fun _ _ _ => False) RR cont) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) I Q RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF name function shape arguments parameters body returnShape installed mf nb nc hup hcont
    (fun _ _ _ _ _ _ _ h => h.elim)

theorem getCodeW_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    (Ch A : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64}
    {Rr Ow : BitVec 64 → Prop} {M1 : Mem} {G1 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 G1)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => GCL Ch A L ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun _ M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G)
      (sourceFunctionBody Guest.guestFn_get_code) := by
  refine uw_heapFact u (fun ⟨p0,hHE,_⟩ => ?_)
  have hwS : ¬ SkWin SKB w := fun h => hwR (u.2.2.2.2.2.2.2.2.2 w (hSk w h))
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_code,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let I0 : GA → Mem → GA → Prop := fun L M G => GCL Ch A L ∧ M = M1 ∧ G = G1
  have up0 : ∀ (x : MlS), ofString "code_hash" ≠ x → ofString "addr" ≠ x →
      ∀ L M G v, I0 L M G → I0 (L.update (x,v)) M G := fun x h1 h2 L M G v ⟨lp,hM,hG⟩ =>
    ⟨gcl_upd lp x v h1 h2,hM,hG⟩
  have ret0 : ∀ (Q' : GA → Mem → GA → Prop) (e : ExpHOL 64), AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w
      (fun _ => False) (fun L M G => I0 L M G ∧ True) Q'
      (fun _ M G => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G) (.return e) := fun _ e =>
    aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG1⟩,_⟩ _ _ => by
      unfold GIs at hG; subst hG; rw [hM,hG1]; exact ust_refl u)
  -- eq = memeq(code_hash, empty_code_hash, 32)
  refine aqgd_roDec _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup
    (memoryFrame_of_good originalRuntimeCode_memeq_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_memeq) (by body_check Guest.guestFn_memeq) (up0 _ (by decide) (by decide)) ?_
  refine aqgd_seq (Q := I0) (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (ret0 _ _)
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- w = htab_get(lds (ts + 48), code_hash)
  refine aqgd_roDec _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup htabGet_memoryFrame
    (by body_check Guest.guestFn_htab_get) (by body_check Guest.guestFn_htab_get) (up0 _ (by decide) (by decide)) ?_
  refine aqgd_seq (Q := I0) (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (ret0 _ _)
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- w = htab_get(lds (bs + 48), code_hash)
  refine aqgd_seq (Q := I0) (aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp) (fun h => h)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun L M G v M' G' pre ⟨e1,e2⟩ => by rw [e1,e2]; exact up0 _ (by decide) (by decide) L M G v pre)) ?_
  refine aqgd_seq (Q := I0) (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (ret0 _ _)
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- k = sk_make(addr, code_hash)
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (∃ a k : BitVec 64, L.lookup (ofString "addr") = some (.val (.word a)) ∧
      L.lookup (ofString "key") = some (.val (.word k))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' v M' G' => v = .val (.word SKB) ∧ G' = G0' ∧ ∀ x, ¬ SkWin SKB x → M' x = M0' x)
    (Pc := fun L M G => (GCL Ch A L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M1 M G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ vmLookup_sk_make (by simp)
    (fun _ M0' G0' _ => skMake_aqgd (fun g h => h.1.1.1.2) hwS M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ _ G hG ⟨⟨lc,la⟩,_,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,la,lc] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) vmLookup_sk_make] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,Ch,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨ev,eG,fr⟩ _
    subst ev hM hG
    exact ⟨⟨gcl_upd lp _ _ (by decide) (by decide),lookup_update_eq' _ _ _⟩,
      ust_of_sk wsf u (SkWin SKB) hSk hSkSO fr eG⟩
  -- htab_set(lds (ts + 40), k, 1); c = ws_get_code(code_hash); return c
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun _ => True)
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) (by omega) hwk hwR hwO)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h.2)
  refine uw_heapFact u2 (fun ⟨p2,_,_⟩ => ?_)
  have u2' := u2
  obtain ⟨hH2,hn2,bg2,_,reg2,_⟩ := u2'
  have cell40 : M2 (Ts + 40#64) = .word (T k40) := by
    obtain ⟨l,_,mem,_⟩ := reg2
    rw [← hc40]; exact (mem k40).1
  refine aqgd_of_arenaFact (Φ := G2.lookup (ofString "ts") = some (.val (.word Ts)))
    (fun _ _ g aw ⟨_,_,hg⟩ => by
      rw [hg] at aw
      obtain ⟨eg,_⟩ := aw.1.1.1.1.1.2.2.2 (ofString "ts") (by decide)
      rw [eg]; exact hTs) (fun gts => ?_)
  refine aqgd_seq (Q := fun L M G => (GCL Ch A L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G)
    (aqgd_conseq (aqgd_keepBal bk (BA := BA) (IA := IA) (IS := IS) (KB := KB) (Ix := Ix)
      (by simp [keepsG,balWatched,goodBal,balExtra])
      (aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_call_regSetJ
        (LP := fun L => GCL Ch A L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ne40 _ _ _ SKB 1#64 reg2
        hH2 hn2 p2 hwP hr2 (fun s hM hG ⟨_,lk⟩ vs ev => ?_))
        (by simp only [keepsG]; decide) (by simp only [keepsG]; decide) (by simp only [keepsG]; decide)))
      (fun L M G h => ⟨h,by rw [h.2.2]; exact bg2⟩)
      (fun L M G ⟨⟨lp,rp⟩,bg⟩ => ⟨lp,ust_of_rp wsf u2 rp bg⟩) (fun _ _ _ h => h.1)) ?_
  · obtain ⟨v1,vs1,rfl,e1,r1⟩ := evalList_cons' s _ _ _ ev
    obtain ⟨v2,vs2,rfl,e2,r2⟩ := evalList_cons' s _ _ _ r1
    obtain ⟨v3,vs3,rfl,e3,r3⟩ := evalList_cons' s _ _ _ r2
    have := evalList_nil' s _ r3; subst this
    have ea : EV s (.op .add [.var .global (ofString "ts"),.const 40#64]) = some (.val (.word (Ts + 40#64))) := by
      simp [EV,evalHOLExact,evalListHOLExact,hG,gts,wordOpHOL,wordOp,valueIsWord,valueWord]
    have := eval_load_word_some s _ _ ea v1 e1
    rw [hM,cell40] at this
    simp [EV,evalHOLExact,lk] at e2
    simp [EV,evalHOLExact] at e3
    subst this e2 e3
    rfl
  refine aqgd_roDec (I := fun L M G => (GCL Ch A L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ∧
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A2 R2 H2 Rr2 Ow2 M2 M G) _ _ _ _ _ _ _
    originalRuntimeCode_wsGetCode_lookup
    (memoryFrame_of_good originalRuntimeCode_wsGetCode_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_ws_get_code) (by body_check Guest.guestFn_ws_get_code)
    (fun L M G v ⟨⟨lp,lk⟩,st⟩ => ⟨⟨gcl_upd lp _ _ (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact lk⟩,st⟩) ?_
  exact aqgd_return _ (fun s v H' _ hG ⟨_,st⟩ _ _ => by unfold GIs at hG; subst hG; exact ⟨trivial,st⟩)

#print axioms getCodeW_aqgd
/-- The world-level declared call `name = get_code(ech, ea)`. -/
theorem aqgd_decCall_gcW (bk : BalKeep) (wsf : WsIFrame WsI) {k40 : Fin n} (ne40 : k40 ≠ ko) (Ts : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hc40 : c k40 = Ts + 40#64)
    (hSkSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSk : ∀ x, SkWin SKB x → Sk x)
    {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ech ea : ExpHOL 64) {cont : ProgHOL 64}
    (Ch A : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64}
    {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M2 → s.globals = G2 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ech,ea] =
        some [.val (.word Ch),.val (.word A)])
    (hres : ∀ (L : GA) (a b : BitVec 64) (M : Mem) (G : GA), LP L →
      USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M G →
      Pc (L.update (name,.rStruct [.val (.word a),.val (.word b)])) M G)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2) Q RR
      (.decCall name (.comb [.one,.one]) (ofString "get_code") [ech,ea] cont) := by
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => GCL Ch A L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ _ M' G' => USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M' G')
    _ _ _ _ _ _ _ originalRuntimeCode_getCode_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact aqgd_conseq (getCodeW_aqgd bk wsf ne40 Ts hTs hc40 hSkSO hSk Ch A u hwP hwk hwR hwO) (fun _ _ _ h => h)
        (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ hc
    (fun L _ _ L' M' G' ⟨lp,_,_⟩ q => hq L L' M' G' lp q)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG2⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG2 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_getCode_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ st sh
    obtain ⟨a,b,rfl⟩ := shape2r sh
    exact hres L a b M' G' lp st

#print axioms aqgd_decCall_gcW
end gc
end InitECandidate.Runtime
