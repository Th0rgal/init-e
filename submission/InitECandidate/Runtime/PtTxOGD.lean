import InitECandidate.Runtime.PtRestAllOGD
import InitECandidate.Runtime.PtSufBOGD
/-!
The actual `process_transaction` body with the interpreter output record threaded through the suffix. `PmcCX` is the
named interpreter contract (conditional until the interpreter proves it): `PmcC` together with the returned output record
`out = Y` (`[Y, Y + 96)` below the exit heap pointer and outside every registry footprint) and its release marks
(`OutRec`). The suffix (spine drops 99 on) runs at the arena bound raised to the exit heap pointer, with the record words
as outside words and the exit memory as base, so the marks are still there at the frame release.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section lw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- A triple over the process arena with its bound raised to the entry heap pointer `Hc ≥ P0` holds over the arena. -/
theorem aqgd_jwsbus_lower {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {Hc : BitVec 64} (le : P0.toNat ≤ Hc.toNat)
    (h : AQGD D B (JWSBUS SP0 Hc FM G0 J C SKB Bo U Sc) w Vn P Q RR p) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => P L M G ∧ HeapIs G Hc) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,hc⟩
  unfold GIs at hH; subst hH
  have awH : JWSBUS SP0 Hc FM G0 J C SKB Bo U Sc s.globals :=
    ⟨⟨⟨⟨⟨(aw_raise aw.1.1.1.1.1 hc).1,aw.1.1.1.1.2⟩,aw.1.1.1.2⟩,aw.1.1.2⟩,aw.1.2⟩,aw.2⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awH sl _ rfl pre
  exact ⟨m,fun cont => let x := a cont; ⟨⟨⟨⟨⟨(aw_lower x.1.1.1.1.1 le).1,x.1.1.1.1.2⟩,x.1.1.1.2⟩,x.1.1.2⟩,x.1.2⟩,x.2⟩,
    n,r,c,b⟩

#print axioms aqgd_jwsbus_lower
end lw

/-- The interpreter output record `[Y, Y + 96)`. -/
def ORec (Y x : BitVec 64) : Prop := Y.toNat ≤ x.toNat ∧ x.toNat < Y.toNat + 96

/-- Named interpreter contract (conditional until the interpreter proves it): `PmcC` and the returned output record. -/
def PmcCX (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (w : BitVec 64) (n : Nat)
    (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (body : ProgHOL 64) : Prop :=
  ∀ (H1 Nj : BitVec 64) (M0 : Mem),
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => True)
      (fun _ M G => RegT n c T Out H1 M D B ko ∧ M = M0 ∧ HeapIs G H1 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun v M' G' => ∃ Y H' : BitVec 64, v = .val (.word Y) ∧ HeapIs G' H' ∧ H1.toNat ≤ Y.toNat ∧
        Y.toNat + 96 ≤ H'.toNat ∧ RegT n c T (fun x => Out x ∨ ORec Y x) H' M' D B ko ∧
        (∃ Nj' : BitVec 64, G'.lookup (ofString "journal_n") = some (.val (.word Nj'))) ∧
        (∀ x, Out x → ¬ Excl x → M' x = M0 x) ∧ OutRec SP0 FM Y M')
      body

section pm
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem}

/-- `out = process_message_call(e)` under `PmcCX`: the continuation runs at the arena bound raised to the exit heap
pointer `Hp`, with `out = Y`, the record words as outside words of the registry, and the exit memory `Mp` as base. -/
theorem aqgd_decCall_pmcX {Q Q2 : GA → Mem → GA → Prop} (Ix : BitVec 64) (e : ExpHOL 64) {cont : ProgHOL 64}
    (p0 : P0.toNat ≤ H0.toNat) (pc : PmcCX SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_process_message_call))
    (hcont : ∀ (Y Hp : BitVec 64) (Mp : Mem), P0.toNat ≤ Y.toNat → Y.toNat + 96 ≤ Hp.toNat →
      OutRec SP0 FM Y Mp → (∀ x, Out x → ¬ Excl x → Mp x = M0 x) →
      AQGD D B (JWSBUS SP0 Hp FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => LPSo Y Ix L ∧ PXR n c T (fun x => Out x ∨ ORec Y x) ko D B Excl Hp Mp M G) Q RR cont)
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
        (∀ x, Out x → ¬ Excl x → M' x = M0' x) ∧ OutRec SP0 FM Y M')
    (Pc := fun L M G => ∃ q : BitVec 64 × BitVec 64 × Mem, ((LPSo q.1 Ix L ∧
      PXR n c T (fun x => Out x ∨ ORec q.1 x) ko D B Excl q.2.1 q.2.2 M G) ∧ HeapIs G q.2.1) ∧
      (P0.toNat ≤ q.1.toNat ∧ q.1.toNat + 96 ≤ q.2.1.toNat ∧ OutRec SP0 FM q.1 q.2.2 ∧
        ∀ x, Out x → ¬ Excl x → q.2.2 x = M0 x))
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_processMessageCall_lookup (by simp) ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_
    (aqgd_ex (fun q => aqgd_purePre (fun ⟨p1,p2,orc,fr⟩ => aqgd_jwsbus_lower (by omega)
      (hcont q.1 q.2.1 q.2.2 p1 p2 orc fr)))) hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,reg,hn,_⟩
    refine aqgd_conseq (pc H1 Nj M0') ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',hH',Y,H',ev,hH2,hY,hYH,reg',⟨Nj',hn'⟩,fr',orc⟩ _
    have e := heapIs_unique hH hH'
    subst e ev
    have p1 : P0.toNat ≤ Y.toNat := by omega
    exact ⟨(Y,H',M'),⟨⟨⟨lps_upd lp _ _ (by decide) (by decide),lookup_update_eq' _ _ _⟩,
      H',Nj',hH2,le_refl _,reg',hn',fun _ _ _ => rfl⟩,hH2⟩,p1,hYH,orc,
      fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_pmcX
end pm
end InitECandidate.Runtime
