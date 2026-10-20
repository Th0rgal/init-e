import InitECandidate.Runtime.PtIdxStartGD
import InitECandidate.Runtime.OriginalGetPreTxStorageCode
/-!
The actual `idx_start_storage(addr, key)` in the block-access-list builder world: the index key (`bal_index`, `addr`,
`key`) in the key buffer, the read-only index lookup (a hit returns the recorded value), else the pre-state storage value
(`get_pre_tx_storage`), stored in a fresh 32-byte entry recorded in `bal_idx_stor`. Every return is a world step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shape4r {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one,.one,.one]) = true) :
    ∃ a b c d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)] := by
  rcases v with ⟨⟨x⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨⟨⟨a⟩⟩ | _ | _,_ | ⟨⟨⟨b⟩⟩ | _ | _,_ | ⟨⟨⟨c⟩⟩ | _ | _,_ | ⟨⟨⟨d⟩⟩ | _ | _,_ | ⟨_,_⟩⟩⟩⟩⟩ <;>
      simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact,shapeEqHOL] at h

/-- The fresh-block state for a `Z`-byte entry at `H3`. -/
def FBMz (Z : Nat) (BA IA IS KB Ix H3 Nj : BitVec 64) (M3 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G H' ∧ H3.toNat + Z ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ BalG BA IA IS KB Ix G ∧
    ∀ x, x.toNat < H3.toNat → M x = M3 x

section fz
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {BA IA IS KB Ix H3 Nj : BitVec 64} {M3 : Mem} {Z : Nat}

theorem aqgd_freshZ {LP : GA → Prop} {p : ProgHOL 64} (Win : BitVec 64 → Prop)
    (hWin : ∀ x, Win x → H3.toNat ≤ x.toNat)
    (h : ∀ M2 G2, FBMz Z BA IA IS KB Ix H3 Nj M3 M2 G2 → AQGD D B A w Vn (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ G = G2 ∧ ∀ x, ¬ Win x → M x = M2 x) RR p) :
    AQGD D B A w Vn (fun L M G => LP L ∧ FBMz Z BA IA IS KB Ix H3 Nj M3 M G)
      (fun L M G => LP L ∧ FBMz Z BA IA IS KB Ix H3 Nj M3 M G) RR p :=
  aqgd_ghostR (fun M2 G2 fb => aqgd_conseq (h M2 G2 fb) (fun _ _ _ h => h)
    (fun L M G ⟨lp,hG,fr⟩ => by
      subst hG
      obtain ⟨H',hH,le,hE,hn,bg,fr0⟩ := fb
      exact ⟨lp,H',hH,le,hE,hn,bg,fun x hx => (fr x (fun hw => by have := hWin x hw; omega)).trans (fr0 x hx)⟩)
    (fun _ _ _ h => h))

theorem aqgd_freshStoreZ {LP : GA → Prop} (d v : ExpHOL 64) (a : BitVec 64) (k : Nat)
    (hw : w.toNat < H3.toNat) (ha : H3.toNat ≤ a.toNat) (hak : a.toNat + 8 * k ≤ 33806089496)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → EV s d = some (.val (.word a)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals → ∀ x, EV s v = some x →
      (flattenHOL x).length ≤ k) :
    AQGD D B A w Vn (fun L M G => LP L ∧ FBMz Z BA IA IS KB Ix H3 Nj M3 M G)
      (fun L M G => LP L ∧ FBMz Z BA IA IS KB Ix H3 Nj M3 M G) RR (.store d v) := by
  have ej : ∀ j, j < k → (a + BitVec.ofNat 64 (8 * j)).toNat = a.toNat + 8 * j := fun j hj => by
    rw [BitVec.toNat_add]; simp; omega
  refine aqgd_freshZ (fun x => ∃ j, j < k ∧ x = a + BitVec.ofNat 64 (8 * j)) (fun x ⟨j,hj,e⟩ => by
    subst e; rw [ej j hj]; omega) (fun M2 G2 _ => aqgd_storeV d v (fun s _ _ ⟨lp,hM,hG⟩ =>
      ⟨a,k,hd s lp,hv s lp,fun j hj e => by have := ej j hj; rw [← e] at this; omega,
        fun M' fr => ⟨lp,hG,fun x hx => by rw [← hM]; exact fr x (fun j hj e => hx ⟨j,hj,e⟩)⟩⟩))

#print axioms aqgd_freshStoreZ
end fz

section st
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko kB : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Nj : BitVec 64}

/-- `memcpy(kb + 28, key, 32)` in the world. -/
theorem aqgd_memcpy_kb28W (wsf : WsIFrame WsI) {LP : GA → Prop} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2) (hHE : H.toNat ≤ 33806089496)
    (hwk : ¬ Rg .kb w) (K : BitVec 64) (hl : ∀ L, LP L → L.lookup (ofString "kb") = some (.val (.word KB)) ∧
      L.lookup (ofString "key") = some (.val (.word K))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 28#64],
        .var .local (ofString "key"),.const 32#64]) := by
  obtain ⟨al,fit,inR⟩ := uw_kb u hHE
  have hin : ∀ x, MWin (KB + 28#64) (32#64 : BitVec 64).toNat x → Rg .kb x := fun x hx =>
    let ⟨a,b⟩ := mwin_kb (off := 28) (n := 32) al fit (by decide) hx; inR x a b
  exact aqgd_conseq (aqgd_call_memcpyW (LP := LP) _ _ _ (KB + 28#64) K 32#64 M2 G2 (by decide)
      (fun h => hwk (hin w h)) (fun s _ _ _ lp => by
        obtain ⟨lk,la⟩ := hl _ lp
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,lk,la,wordOpHOL,wordOp,valueIsWord,valueWord]))
    (fun _ _ _ h => h) (fun L M G ⟨lp,hG,fr⟩ => ⟨lp,ust_of_kb wsf u _ hin fr hG⟩) (fun _ _ _ h => h)

/-- `htab_set(bal_idx_stor, kb, rec)` in the world. -/
theorem aqgd_setIS_W (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (hwis : ¬ Rg .is w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (R : BitVec 64)
    (hl : ∀ L, LP L → L.lookup (ofString "kb") = some (.val (.word KB)) ∧
      L.lookup (ofString "rec") = some (.val (.word R))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "htab_set") [.var .global (ofString "bal_idx_stor"),
        .var .local (ofString "kb"),.var .local (ofString "rec")]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_call_htabSet_o bk BA IA IS KB Ix (LP := LP) _ _ _ IS KB R H Nj (Rg .is) M2 G2
      (bw.1 .is trivial) hH hn bg hwis hwP p0 (fun s _ hG lp => by
        obtain ⟨lk,lr⟩ := hl _ lp
        have gi : s.globals.lookup (ofString "bal_idx_stor") = some (.val (.word IS)) := by
          rw [hG]; exact bg.2.2.1
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,lk,lr,gi]))
    (fun _ _ _ h => h)
    (fun L M G ⟨⟨lp,H',hH',le,hn',tob,fr⟩,bg'⟩ => ⟨lp,ust_of_comp wsf .is trivial u le hH' hn' bg' tob
      (fun x hx hr => fr x hr hx)⟩) (fun _ _ _ h => h)

#print axioms aqgd_setIS_W

/-- The world-level declared call `name = get_pre_tx_storage(ea, ek)`. -/
theorem aqgd_decCall_gpsW (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (ea ek : ExpHOL 64)
    {cont : ProgHOL 64} (A K : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64}
    {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 G2)
    (p0 : P0.toNat ≤ H.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w) (hwO : ¬ Ow w)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M2 → s.globals = G2 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [ea,ek] =
        some [.val (.word A),.val (.word K)])
    (hres : ∀ (L : GA) (a b c' d : BitVec 64) (M : Mem) (G : GA), LP L →
      USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M2 M G →
      Pc (L.update (name,.rStruct [.val (.word a),.val (.word b),.val (.word c'),.val (.word d)])) M G)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2) Q RR
      (.decCall name (.comb [.one,.one,.one,.one]) (ofString "get_pre_tx_storage") [ea,ek] cont) := by
  have u' := u
  obtain ⟨hH,hn,bg,_,reg,wi,rB,dRO,_⟩ := u'
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ _ _ _ M' G' => GPPost n c T Out D B ko WsI BA IA IS KB Ix Rr Ow H Nj M2 M' G')
    _ _ _ _ _ _ _ originalRuntimeCode_getPreTxStorage_lookup (by simp)
    (fun L0 M0' G0' ⟨_,hM,hG⟩ => by
      rw [hM,hG]
      exact aqgd_conseq (getPreStor_aqgd bk BA IA IS KB Ix WsI wsr ne Bs hBs hcB A K H Nj Rr Ow M2 G2 reg rB dRO hH hn
        bg wi p0 hwP hwR hwO) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h)) ?_ (fun h => h.elim) ?_ hc
    (fun L _ _ L' M' G' ⟨lp,_,_⟩ q => hq L L' M' G' lp q)
  · intro F s values callee rs _ dom H' hG ⟨lp,hM,hG2⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG2 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    have e := callee_eq originalRuntimeCode_getPreTxStorage_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,_,_⟩ gp sh
    obtain ⟨a,b,c',d,rfl⟩ := shape4r sh
    exact hres L a b c' d M' G' lp (ust_of_gp wsr.1 u gp)

#print axioms aqgd_decCall_gpsW
/-- Locals of the storage tail. -/
def ISL (KB A K R : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "kb") = some (.val (.word KB)) ∧ L.lookup (ofString "addr") = some (.val (.word A)) ∧
  L.lookup (ofString "key") = some (.val (.word K)) ∧ L.lookup (ofString "rec") = some (.val (.word R))

/-- The `idx_start_storage` tail program. -/
def idxStorTailP : ProgHOL 64 :=
  (ProgHOL.call (some (none,none)) (ofString "st_le64") [.var .local (ofString "kb"),
      .var .global (ofString "bal_index")]).seq
    ((ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 8#64],
        .var .local (ofString "addr"),.const 20#64]).seq
      ((ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 28#64],
          .var .local (ofString "key"),.const 32#64]).seq
        ((ProgHOL.call (some (none,none)) (ofString "htab_set") [.var .global (ofString "bal_idx_stor"),
            .var .local (ofString "kb"),.var .local (ofString "rec")]).seq
          (.return (.var .local (ofString "v"))))))

theorem idxStorTail_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) (A K R : BitVec 64) {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M4 : Mem} {G4 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M4 G4)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ISL KB A K R L ∧ M = M4 ∧ G = G4) (fun _ _ _ => False)
      (fun _ M G => USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M4 M G) idxStorTailP := by
  unfold idxStorTailP
  refine uw_heapFact u (fun ⟨p0,hHE,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ISL KB A K R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M4 M G)
    (aqgd_stLe64_kbW wsf u hHE (hwk .kb trivial) (fun L h => h.1)) ?_
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun _ => True)
    (fun A5 R5 H5 Rr5 Ow5 M5 G5 u5 le5 hk5 hr5 ho5 => ?_) (by omega) hwk hwR hwO)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h.2)
  refine uw_heapFact u5 (fun ⟨_,hHE5,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ISL KB A K R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A5 R5 H5 Rr5 Ow5 M5 M G)
    (aqgd_memcpy_kbW wsf u5 hHE5 (hk5 .kb trivial) A (fun L h => ⟨h.1,h.2.1⟩)) ?_
  refine aqgd_ust (fun A6 R6 H6 Rr6 Ow6 M6 G6 u6 le6 hk6 hr6 ho6 => ?_) (by omega) hk5 hr5 ho5
  refine uw_heapFact u6 (fun ⟨_,hHE6,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ISL KB A K R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A6 R6 H6 Rr6 Ow6 M6 M G)
    (aqgd_memcpy_kb28W wsf u6 hHE6 (hk6 .kb trivial) K (fun L h => ⟨h.1,h.2.2.1⟩)) ?_
  refine aqgd_ust (fun A7 R7 H7 Rr7 Ow7 M7 G7 u7 le7 hk7 hr7 ho7 => ?_) (by omega) hk6 hr6 ho6
  refine uw_heapFact u7 (fun ⟨p7,_,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ISL KB A K R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A7 R7 H7 Rr7 Ow7 M7 M G)
    (aqgd_setIS_W bk wsf u7 (hk7 .is trivial) hwP p7 R (fun L h => ⟨h.1,h.2.2.2⟩)) ?_
  exact aqgd_return _ (fun s v _ _ hG ⟨_,st⟩ _ _ => by unfold GIs at hG; subst hG; exact ⟨trivial,st⟩)

#print axioms idxStorTail_aqgd

/-- The entry block `rec = alloc(32); st rec, v;` and the tail. -/
def idxStorRecP : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "alloc") [.const 32#64]
    ((ProgHOL.store (.var .local (ofString "rec")) (.var .local (ofString "v"))).seq idxStorTailP)

theorem idxStorRec_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) (A K a b c' d : BitVec 64) {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H3 : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M3 : Mem} {G3 : GA}
    (u3 : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H3 Rr Ow M3 G3)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "kb") = some (.val (.word KB)) ∧
        L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "key") = some (.val (.word K)) ∧
        L.lookup (ofString "v") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c'),.val (.word d)])) ∧
        M = M3 ∧ G = G3) (fun _ _ _ => False)
      (fun _ M G => USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H3 Rr Ow M3 M G) idxStorRecP := by
  refine uw_heapFact u3 (fun ⟨p0,hHE,hal⟩ => ?_)
  have hw3 : w.toNat < H3.toNat := by omega
  have u3' := u3
  obtain ⟨hH3,hn3,hB3,_⟩ := u3'
  let LPf : GA → Prop := fun L => ISL KB A K H3 L ∧
    L.lookup (ofString "v") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c'),.val (.word d)])
  unfold idxStorRecP
  refine aqgd_decCall_alloc_b bk BA IA IS KB Ix
    (Pc := fun L M G => (LPf L ∧ FBMz 32 BA IA IS KB Ix H3 Nj M3 M G) ∧ H3.toNat + 32 ≤ 33806089496)
    (Qc := fun _ _ _ => False) (ofString "rec") 32#64 H3 Nj M3 G3 hH3 hn3 hB3 ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro L H' G' ⟨lk,la,lkey,lv⟩ hH' le hE _ hn' bg'
    have e32 : (32#64 : BitVec 64).toNat = 32 := by decide
    rw [e32] at le
    exact ⟨⟨⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lkey,lookup_update_eq' _ _ _⟩,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lv⟩,H',hH',le,hE,hn',bg',fun _ _ => rfl⟩,by omega⟩
  refine aqgd_pureE (fun hfit => ?_)
  refine aqgd_seq (aqgd_freshStoreZ _ _ H3 4 hw3 (le_refl _) (by omega)
    (fun s h => by simp [EV,evalHOLExact,h.1.2.2.2])
    (fun s h x hx => by simp [EV,evalHOLExact,h.2] at hx; subst hx; simp [flattenHOL])) ?_
  refine aqgd_ghostR (fun M4 G4 fb => ?_)
  obtain ⟨H4,hH4,le4,_,hn4,bg4,fr4⟩ := fb
  obtain ⟨A4,R4,H4',Rr4,Ow4,u4,le',sub',gr',grR',grO',fr'⟩ :=
    ust_of_fresh (M := M4) (G := G4) wsf u3 (by omega : H3.toNat ≤ H4.toNat) hH4 hn4 bg4 fr4
  refine aqgd_conseq (idxStorTail_aqgd bk wsf A K H3 u4 hwP (fun k hk h => ?_) (fun h => ?_) (fun h => ?_))
    (fun L M G ⟨⟨itl,_⟩,hM,hG⟩ => ⟨itl,hM,hG⟩) (fun _ _ _ h => h)
    (fun v M G s2 => ust_trans le' sub' gr' grR' grO' fr' s2)
  · rcases gr' k hk w h with ⟨l1,h1⟩ | ⟨a1,_⟩
    · exact hwk k l1 h1
    · omega
  · rcases grR' w h with h | ⟨a1,_⟩
    · exact hwR h
    · omega
  · rcases grO' w h with h | ⟨a1,_⟩
    · exact hwO h
    · omega

#print axioms idxStorRec_aqgd

/-- The actual `idx_start_storage(addr, key)`: every return is a world step. -/
theorem idxStartStor_aqgd (bk : BalKeep) (wsr : WsReadObl D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) WsI)
    (ne : kB ≠ ko) (Bs : BitVec 64) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (A K : BitVec 64) {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop}
    {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M1 : Mem} {G1 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 G1)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
        L.lookup (ofString "key") = some (.val (.word K))) ∧ M = M1 ∧ G = G1) (fun _ _ _ => False)
      (fun _ M G => USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G)
      (sourceFunctionBody Guest.guestFn_idx_start_storage) := by
  refine uw_heapFact u (fun ⟨p0,hHE,_⟩ => ?_)
  have u' := u
  obtain ⟨hH,hn,bg,_⟩ := u'
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_idx_start_storage,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let LPk : GA → Prop := fun L => L.lookup (ofString "kb") = some (.val (.word KB)) ∧
    L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "key") = some (.val (.word K))
  refine aqgd_decD (Pb := fun L M G => LPk L ∧ M = M1 ∧ G = G1)
    (Qb := fun _ _ _ => False) (ofString "kb") .one _ (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H'' _ _ hG ⟨⟨la,lk⟩,hM,hG1⟩ _ ev _
    unfold GIs at hG
    have gk : s.globals.lookup (ofString "bal_key_buf") = some (.val (.word KB)) := by
      rw [hG,hG1]; exact bg.2.2.2.1
    simp [EV,evalHOLExact,gk] at ev; subst ev
    exact ⟨⟨lookup_update_eq' _ _ _,by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lk⟩,hM,hG1⟩
  refine aqgd_seq (Q := fun L M G => LPk L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj ADs Rg H Rr Ow M1 M G)
    (aqgd_stLe64_kbW wsr.1 u hHE (hwk .kb trivial) (fun L h => h.1)) ?_
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun _ => True)
    (fun A2 R2 H2 Rr2 Ow2 M2 G2 u2 le2 hk2 hr2 ho2 => ?_) (by omega) hwk hwR hwO)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h.2)
  refine uw_heapFact u2 (fun ⟨_,hHE2,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => LPk L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A2 R2 H2 Rr2 Ow2 M2 M G)
    (aqgd_memcpy_kbW wsr.1 u2 hHE2 (hk2 .kb trivial) A (fun L h => ⟨h.1,h.2.1⟩)) ?_
  refine aqgd_ust (fun A3 R3 H3 Rr3 Ow3 M3 G3 u3 le3 hk3 hr3 ho3 => ?_) (by omega) hk2 hr2 ho2
  refine uw_heapFact u3 (fun ⟨_,hHE3,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => LPk L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A3 R3 H3 Rr3 Ow3 M3 M G)
    (aqgd_memcpy_kb28W wsr.1 u3 hHE3 (hk3 .kb trivial) K (fun L h => ⟨h.1,h.2.2⟩)) ?_
  refine aqgd_ust (fun A4 R4 H4 Rr4 Ow4 M4 G4 u4 le4 hk4 hr4 ho4 => ?_) (by omega) hk3 hr3 ho3
  refine uw_heapFact u4 (fun ⟨p4,_,_⟩ => ?_)
  -- m = htab_get(bal_idx_stor, kb): read-only
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => LPk L ∧ M = M4 ∧ G = G4)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨⟨lk,la,lkey⟩,hM,hG⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lkey⟩,hM,hG⟩
  refine aqgd_seq (Q := fun L M G => LPk L ∧ M = M4 ∧ G = G4) (aqgd_ite (CT := fun _ _ _ => True)
      (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H' _ hG ⟨⟨_,hM,hG4⟩,_⟩ _ _ => by
        unfold GIs at hG; subst hG
        rw [hM,hG4]
        exact ⟨trivial,ust_refl u4⟩))
      (aqgd_conseq aqgd_skip (fun L M G h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- v = get_pre_tx_storage(addr, key)
  refine aqgd_decCall_gpsW bk wsr ne Bs hBs hcB (LP := LPk)
    (Pc := fun L M G => ∃ q : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64, (LPk L ∧
      L.lookup (ofString "v") = some (.rStruct [.val (.word q.1),.val (.word q.2.1),.val (.word q.2.2.1),
        .val (.word q.2.2.2)])) ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Nj A4 R4 H4 Rr4 Ow4 M4 M G)
    (Qc := fun _ _ _ => False) (ofString "v") _ _ A K u4 p4 hwP hr4 ho4 ?_ ?_ ?_ (fun _ _ _ _ _ h => h.elim)
  · intro F s _ _ _ ⟨_,la,lkey⟩
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,la,lkey]
  · intro L a b c' d M G ⟨lk,la,lkey⟩ st
    exact ⟨(a,b,c',d),⟨⟨by rw [lookup_update_ne' _ _ (by decide)]; exact lk,by rw [lookup_update_ne' _ _ (by decide)]; exact la,
      by rw [lookup_update_ne' _ _ (by decide)]; exact lkey⟩,lookup_update_eq' _ _ _⟩,st⟩
  refine aqgd_ex (fun q => ?_)
  rcases q with ⟨a,b,c',d⟩
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun _ => True)
    (fun A5 R5 H5 Rr5 Ow5 M5 G5 u5 le5 hk5 hr5 ho5 => ?_) (by omega) hk4 hr4 ho4)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)
  exact aqgd_conseq (idxStorRec_aqgd bk wsr.1 A K a b c' d u5 hwP hk5 hr5 ho5)
    (fun L M G ⟨⟨⟨lk,la,lkey⟩,lv⟩,hM,hG⟩ => ⟨⟨lk,la,lkey,lv⟩,hM,hG⟩) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => ⟨trivial,h⟩)

#print axioms idxStartStor_aqgd
end st
end InitECandidate.Runtime
