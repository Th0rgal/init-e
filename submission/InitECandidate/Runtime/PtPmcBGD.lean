import InitECandidate.Runtime.PtTxOGD
import InitECandidate.Runtime.PtArenaBalGD
/-!
The interpreter contract with the `bal_*` globals and an exit snapshot (`PmcCXB`, named, OPEN until the actual
`process_message_call` proof instantiates it): `PmcCX` together with the one-word `bal_*` globals at exit and a snapshot
`SNAP` of the exit memory relative to them and to the output record. `out = process_message_call(m)` under `PmcCXB`
hands the continuation the pinned `bal_*` globals and the snapshot (a pure fact about the exit memory `Mp`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Named interpreter contract with the `bal_*` globals and the exit snapshot (staging, OPEN). -/
def PmcCXB (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (w : BitVec 64) (n : Nat)
    (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop)
    (SNAP : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Mem → Prop)
    (body : ProgHOL 64) : Prop :=
  ∀ (H1 Nj : BitVec 64) (M0 : Mem),
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => True)
      (fun _ M G => RegT n c T Out H1 M D B ko ∧ M = M0 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun v M' G' => ∃ Y H' : BitVec 64, v = .val (.word Y) ∧ HeapIs G' H' ∧ H1.toNat ≤ Y.toNat ∧
        Y.toNat + 96 ≤ H'.toNat ∧ RegT n c T (fun x => Out x ∨ ORec Y x) H' M' D B ko ∧
        (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
        (∀ x, Out x → ¬ Excl x → M' x = M0 x) ∧ OutRec SP0 FM Y M' ∧
        ∃ BA IA IS KB Ixb : BitVec 64, BalG BA IA IS KB Ixb G' ∧ SNAP BA IA IS KB Ixb Y H' M')
      body

section pm
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem}
  {SNAP : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Mem → Prop}

/-- `out = process_message_call(e)` under `PmcCXB`: the continuation runs at the arena bound raised to the exit heap
pointer `Hp`, with `out = Y`, the record words as outside words of the registry, the exit memory `Mp` as base, the
`bal_*` globals at their exit words and the exit snapshot. -/
theorem aqgd_decCall_pmcXB {Q Q2 : GA → Mem → GA → Prop} (Ix : BitVec 64) (e : ExpHOL 64) {cont : ProgHOL 64}
    (p0 : P0.toNat ≤ H0.toNat) (pc : PmcCXB SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl SNAP
      (sourceFunctionBody Guest.guestFn_process_message_call))
    (hcont : ∀ (Y Hp : BitVec 64) (Mp : Mem) (BA IA IS KB Ixb : BitVec 64), P0.toNat ≤ Y.toNat →
      Y.toNat + 96 ≤ Hp.toNat → OutRec SP0 FM Y Mp → (∀ x, Out x → ¬ Excl x → Mp x = M0 x) →
      SNAP BA IA IS KB Ixb Y Hp Mp →
      AQGD D B (JWSBUS SP0 Hp FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LPSo Y Ix L ∧ PXR n c T (fun x => Out x ∨ ORec Y x) ko D B Excl Hp Mp M G) ∧
          BalG BA IA IS KB Ixb G) Q RR cont)
    (hres : ∀ L M G L' M' G', LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (ofString "out",L.lookup (ofString "out"))) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR
      (.decCall (ofString "out") .one (ofString "process_message_call") [e] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 : BitVec 64, HeapIs G0' H1 ∧ ∃ Y H' : BitVec 64, v = .val (.word Y) ∧ HeapIs G' H' ∧ H1.toNat ≤ Y.toNat ∧
        Y.toNat + 96 ≤ H'.toNat ∧ RegT n c T (fun x => Out x ∨ ORec Y x) H' M' D B ko ∧
        (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
        (∀ x, Out x → ¬ Excl x → M' x = M0' x) ∧ OutRec SP0 FM Y M' ∧
        ∃ BA IA IS KB Ixb : BitVec 64, BalG BA IA IS KB Ixb G' ∧ SNAP BA IA IS KB Ixb Y H' M')
    (Pc := fun L M G => ∃ q : (BitVec 64 × BitVec 64 × Mem) × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
        BitVec 64), (((LPSo q.1.1 Ix L ∧ PXR n c T (fun x => Out x ∨ ORec q.1.1 x) ko D B Excl q.1.2.1 q.1.2.2 M G) ∧
        BalG q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 G) ∧ HeapIs G q.1.2.1) ∧
      (P0.toNat ≤ q.1.1.toNat ∧ q.1.1.toNat + 96 ≤ q.1.2.1.toNat ∧ OutRec SP0 FM q.1.1 q.1.2.2 ∧
        (∀ x, Out x → ¬ Excl x → q.1.2.2 x = M0 x) ∧
        SNAP q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 q.1.1 q.1.2.1 q.1.2.2))
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_processMessageCall_lookup (by simp) ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨p1,p2,orc,fr,sn⟩ => aqgd_jwsbus_lower (by omega)
      (hcont q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 p1 p2 orc fr sn)))) hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,reg,hn,_⟩
    refine aqgd_conseq (pc H1 Nj M0') ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩
      ⟨H1',hH',Y,H',ev,hH2,hY,hYH,reg',⟨Nj',hn'⟩,fr',orc,BA,IA,IS,KB,Ixb,bg,sn⟩ _
    have e := heapIs_unique hH hH'
    subst e ev
    have p1 : P0.toNat ≤ Y.toNat := by omega
    exact ⟨((Y,H',M'),(BA,IA,IS,KB,Ixb)),⟨⟨⟨⟨lps_upd lp _ _ (by decide) (by decide),lookup_update_eq' _ _ _⟩,
      H',Nj',hH2,le_refl _,reg',hn',fun _ _ _ => rfl⟩,bg⟩,hH2⟩,p1,hYH,orc,
      fun x ho hx => (fr' x ho hx).trans (fr x ho hx),sn⟩

#print axioms aqgd_decCall_pmcXB

/-- Entering the arena with the `bal_*` globals pinned at their current words. -/
theorem aqgd_enterB {Vn : MlS → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {BA IA IS KB Ixb : BitVec 64}
    (h : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w Vn P Q RR p) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => P L M G ∧ BalG BA IA IS KB Ixb G) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,bg⟩
  unfold GIs at hH; subst hH
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom ⟨aw,bg⟩ sl _ rfl pre
  exact ⟨m,fun cont => (a cont).1,n,r,c,b⟩

#print axioms aqgd_enterB
end pm
end InitECandidate.Runtime
