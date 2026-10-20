import InitECandidate.Runtime.PtUWStepGD
import InitECandidate.Runtime.OriginalGetPreTxAccountCode
/-!
The actual `idx_start_account(addr)` in the block-access-list builder world: the index key (`bal_index`, `addr`)
written into the key buffer, the read-only index lookup (a hit returns the recorded entry), else the pre-state account
(`get_pre_tx_account`), a fresh 80-byte entry initialised from it, the key rewritten and the entry recorded in the
account index table `bal_idx_accts` (`htab_set` on the owned index table). Every return is a world step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A byte window inside the 64-byte key buffer. -/
theorem mwin_kb {KB x : BitVec 64} {off n : Nat} (hal : KB.toNat % 8 = 0) (fit : KB.toNat + 64 < 2 ^ 64)
    (h : off + n ≤ 64) (hx : MWin (KB + BitVec.ofNat 64 off) n x) : KB.toNat ≤ x.toNat ∧ x.toNat < KB.toNat + 64 := by
  have e : (KB + BitVec.ofNat 64 off).toNat = KB.toNat + off := by
    rw [BitVec.toNat_add]; simp; omega
  obtain ⟨j,hj,hx | hx⟩ := hx
  · have e2 : (KB + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = KB.toNat + off + j := by
      rw [BitVec.toNat_add,e]; simp; omega
    subst hx; rw [e2]; omega
  · have e2 : (KB + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = KB.toNat + off + j := by
      rw [BitVec.toNat_add,e]; simp; omega
    subst hx
    rw [panByteAlign_toNat64,e2]
    have := Nat.div_mul_le_self (KB.toNat + off + j) 8
    have := Nat.mod_add_div (KB.toNat + off + j) 8
    have h8 : KB.toNat ≤ (KB.toNat + off + j) / 8 * 8 := by
      have := Nat.le_div_iff_mul_le (show 0 < 8 by decide) |>.mpr (show KB.toNat / 8 * 8 ≤ KB.toNat + off + j by omega)
      omega
    omega

#print axioms mwin_kb

section ia
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}
  {BA IA IS KB Ix : BitVec 64} {n : Nat} {c T : Fin n → BitVec 64}
  {Out : BitVec 64 → Prop} {ko : Fin n} {WsI : Mem → BitVec 64 → (BitVec 64 → Prop) → Prop} {Sk : BitVec 64 → Prop}
  {Nj : BitVec 64}

/-- Locals of the tail of `idx_start_account`. -/
def ITL (KB A R : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "kb") = some (.val (.word KB)) ∧ L.lookup (ofString "addr") = some (.val (.word A)) ∧
  L.lookup (ofString "rec") = some (.val (.word R))

/-- The key buffer of a world: aligned, 64 bytes in its region, below the heap. -/
theorem uw_kb {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop}
    {M : Mem} {G : GA} (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M G)
    (hHE : H.toNat ≤ 33806089496) :
    KB.toNat % 8 = 0 ∧ KB.toNat + 64 < 2 ^ 64 ∧ ∀ x : BitVec 64, KB.toNat ≤ x.toNat → x.toNat < KB.toNat + 64 →
      Rg .kb x := by
  obtain ⟨al,inR⟩ := u.2.2.2.1.1 .kb trivial
  have bl := u.2.2.2.1.2.2 .kb trivial
  have := bl KB (inR KB (le_refl _) (by omega))
  exact ⟨al,by omega,inR⟩

theorem mwin_kb0 {KB x : BitVec 64} {nn : Nat} (hal : KB.toNat % 8 = 0) (fit : KB.toNat + 64 < 2 ^ 64)
    (h : nn ≤ 64) (hx : MWin KB nn x) : KB.toNat ≤ x.toNat ∧ x.toNat < KB.toNat + 64 :=
  mwin_kb (off := 0) (n := nn) hal fit (by omega) (by simpa using hx)

/-- `st_le64(kb, bal_index)` in the world. -/
theorem aqgd_stLe64_kbW (wsf : WsIFrame WsI) {LP : GA → Prop} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2) (hHE : H.toNat ≤ 33806089496)
    (hwk : ¬ Rg .kb w) (hl : ∀ L, LP L → L.lookup (ofString "kb") = some (.val (.word KB))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "st_le64") [.var .local (ofString "kb"),.var .global (ofString "bal_index")]) := by
  obtain ⟨al,fit,inR⟩ := uw_kb u hHE
  have hin : ∀ x, MWin KB 8 x → Rg .kb x := fun x hx =>
    let ⟨a,b⟩ := mwin_kb0 al fit (by decide) hx; inR x a b
  exact aqgd_conseq (aqgd_call_stLe64 (LP := LP) _ _ KB M2 G2 (fun h => hwk (hin w h))
      (fun s _ _ lp => by simp [EV,evalHOLExact,hl _ lp]))
    (fun _ _ _ h => h) (fun L M G ⟨lp,hG,fr⟩ => ⟨lp,ust_of_kb wsf u (MWin KB 8) hin fr hG⟩) (fun _ _ _ h => h)

#print axioms aqgd_stLe64_kbW

/-- `memcpy(kb + 8, addr, 20)` in the world. -/
theorem aqgd_memcpy_kbW (wsf : WsIFrame WsI) {LP : GA → Prop} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2) (hHE : H.toNat ≤ 33806089496)
    (hwk : ¬ Rg .kb w) (A : BitVec 64) (hl : ∀ L, LP L → L.lookup (ofString "kb") = some (.val (.word KB)) ∧
      L.lookup (ofString "addr") = some (.val (.word A))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 8#64],
        .var .local (ofString "addr"),.const 20#64]) := by
  obtain ⟨al,fit,inR⟩ := uw_kb u hHE
  have hin : ∀ x, MWin (KB + 8#64) (20#64 : BitVec 64).toNat x → Rg .kb x := fun x hx =>
    let ⟨a,b⟩ := mwin_kb (off := 8) (n := 20) al fit (by decide) hx; inR x a b
  exact aqgd_conseq (aqgd_call_memcpyW (LP := LP) _ _ _ (KB + 8#64) A 20#64 M2 G2 (by decide)
      (fun h => hwk (hin w h)) (fun s _ _ _ lp => by
        obtain ⟨lk,la⟩ := hl _ lp
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,lk,la,wordOpHOL,wordOp,valueIsWord,valueWord]))
    (fun _ _ _ h => h) (fun L M G ⟨lp,hG,fr⟩ => ⟨lp,ust_of_kb wsf u _ hin fr hG⟩) (fun _ _ _ h => h)

#print axioms aqgd_memcpy_kbW

/-- `htab_set(bal_idx_accts, kb, rec)` in the world. -/
theorem aqgd_setIA_W (bk : BalKeep) (wsf : WsIFrame WsI) {LP : GA → Prop} {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2)
    (hwia : ¬ Rg .ia w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H.toNat) (R : BitVec 64)
    (hl : ∀ L, LP L → L.lookup (ofString "kb") = some (.val (.word KB)) ∧
      L.lookup (ofString "rec") = some (.val (.word R))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => LP L ∧ M = M2 ∧ G = G2)
      (fun L M G => LP L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 M G) RR
      (.call (some (none,none)) (ofString "htab_set") [.var .global (ofString "bal_idx_accts"),
        .var .local (ofString "kb"),.var .local (ofString "rec")]) := by
  have u' := u
  obtain ⟨hH,hn,bg,bw,_⟩ := u'
  exact aqgd_conseq (aqgd_call_htabSet_o bk BA IA IS KB Ix (LP := LP) _ _ _ IA KB R H Nj (Rg .ia) M2 G2
      (bw.1 .ia trivial) hH hn bg hwia hwP p0 (fun s _ hG lp => by
        obtain ⟨lk,lr⟩ := hl _ lp
        have gi : s.globals.lookup (ofString "bal_idx_accts") = some (.val (.word IA)) := by rw [hG]; exact bg.2.1
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,lk,lr,gi]))
    (fun _ _ _ h => h)
    (fun L M G ⟨⟨lp,H',hH',le,hn',tob,fr⟩,bg'⟩ => ⟨lp,ust_of_comp wsf .ia trivial u le hH' hn' bg' tob
      (fun x hx hr => fr x hr hx)⟩) (fun _ _ _ h => h)

#print axioms aqgd_setIA_W

/-- Heap facts of a world on the full arena. -/
theorem uw_heapFact {ADs : Set (BitVec 64)} {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64}
    {Rr Ow : BitVec 64 → Prop} {M2 : Mem} {G2 : GA} {Vn : MlS → Prop} {P Q : GA → Mem → GA → Prop}
    {p : ProgHOL 64} (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M2 G2)
    (h : P0.toNat ≤ H.toNat ∧ H.toNat ≤ 33806089496 ∧ H.toNat % 8 = 0 →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => P L M G ∧ M = M2 ∧ G = G2) Q RR p) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => P L M G ∧ M = M2 ∧ G = G2) Q RR p :=
  aqgd_of_arenaFact (fun _ _ g aw ⟨_,_,hg⟩ => by rw [hg] at aw; exact jws_heap_facts aw.1.1.1 u.1) h

/-- The tail `st_le64(kb, bal_index); memcpy(kb + 8, addr, 20); htab_set(bal_idx_accts, kb, rec); return rec`. -/
theorem idxAcctTail_aqgd (bk : BalKeep) (wsf : WsIFrame WsI) (A R : BitVec 64) {ADs : Set (BitVec 64)}
    {Rg : BalK → BitVec 64 → Prop} {H : BitVec 64} {Rr Ow : BitVec 64 → Prop} {M4 : Mem} {G4 : GA}
    (u : UW D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M4 G4)
    (hwP : w.toNat < P0.toNat) (hwk : ∀ k, BalK.live ADs k → ¬ Rg k w) (hwR : ¬ Rr w) (hwO : ¬ Ow w) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False) (fun L M G => ITL KB A R L ∧ M = M4 ∧ G = G4)
      (fun _ _ _ => False)
      (fun v M G => v = .val (.word R) ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M4 M G)
      ((ProgHOL.call (some (none,none)) (ofString "st_le64") [.var .local (ofString "kb"),
          .var .global (ofString "bal_index")]).seq
        ((ProgHOL.call (some (none,none)) (ofString "memcpy") [.op .add [.var .local (ofString "kb"),.const 8#64],
            .var .local (ofString "addr"),.const 20#64]).seq
          ((ProgHOL.call (some (none,none)) (ofString "htab_set") [.var .global (ofString "bal_idx_accts"),
              .var .local (ofString "kb"),.var .local (ofString "rec")]).seq
            (.return (.var .local (ofString "rec")))))) := by
  refine uw_heapFact u (fun ⟨p0,hHE,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ITL KB A R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj ADs Rg H Rr Ow M4 M G)
    (aqgd_stLe64_kbW wsf u hHE (hwk .kb trivial) (fun L h => h.1)) ?_
  refine aqgd_conseq (aqgd_ust (LP' := fun _ => False) (X := fun v => v = .val (.word R))
    (fun A5 R5 H5 Rr5 Ow5 M5 G5 u5 le5 hk5 hr5 ho5 => ?_) (by omega) hwk hwR hwO)
    (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)
  refine uw_heapFact u5 (fun ⟨p5,hHE5,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ITL KB A R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A5 R5 H5 Rr5 Ow5 M5 M G)
    (aqgd_memcpy_kbW wsf u5 hHE5 (hk5 .kb trivial) A (fun L h => ⟨h.1,h.2.1⟩)) ?_
  refine aqgd_ust (fun A6 R6 H6 Rr6 Ow6 M6 G6 u6 le6 hk6 hr6 ho6 => ?_) (by omega) hk5 hr5 ho5
  refine uw_heapFact u6 (fun ⟨p6,_,_⟩ => ?_)
  refine aqgd_seq (Q := fun L M G => ITL KB A R L ∧ USt D B BA IA IS KB Ix n c T Out ko WsI Sk Nj A6 R6 H6 Rr6 Ow6 M6 M G)
    (aqgd_setIA_W bk wsf u6 (hk6 .ia trivial) hwP p6 R (fun L h => ⟨h.1,h.2.2⟩)) ?_
  exact aqgd_return _ (fun s v _ _ hG ⟨⟨_,_,lr⟩,st⟩ _ ev => by
    simp [EV,evalHOLExact,lr] at ev
    unfold GIs at hG; subst hG
    exact ⟨ev.symm,st⟩)

#print axioms idxAcctTail_aqgd

end ia
end InitECandidate.Runtime
