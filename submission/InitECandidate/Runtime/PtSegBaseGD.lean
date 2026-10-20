import InitECandidate.Runtime.ProcessTxSGD
/-!
Base of the actual `process_transaction` segment from `te_new` (spine drop 34) to `process_message_call`: the segment
state `SI` at the fresh base `Lo` (the heap pointer at drop 34) with its conversions from and to `PXR`, the memory steps
keeping it (writes at or above `Lo`, the Keccak state/pad windows), a word store at or above `Lo` whose normal outcome
learns the address is in the domain, the conjunction of two triples on one program, and lowering a heap-aware triple
proven at the current heap pointer as arena bound.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The Keccak state and pad windows. -/
def KPW (K Pd x : BitVec 64) : Prop := MWin K 200 x ∨ MWin Pd 136 x

/-- Segment state at the fresh base `Lo`: heap pointer at least `Lo`, the content-carrying registry at `Lo` (its
footprint below `Lo`), the journal counter `Nj`, and every outside word outside `Excl` equal to the entry memory. -/
def SI (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (Lo Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  (∃ H : BitVec 64, HeapIs G H ∧ Lo.toNat ≤ H.toNat) ∧ RegT n c T Out Lo M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M x = M0 x

section si
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {D : BitVec 64 → Prop} {B : Bool}
  {Excl : BitVec 64 → Prop} {Lo Nj H0 : BitVec 64} {M0 : Mem}

theorem pxr_of_si {M : Mem} {G : GA} (h0 : H0.toNat ≤ Lo.toNat) (h : SI n c T Out ko D B Excl Lo Nj M0 M G) :
    PXR n c T Out ko D B Excl H0 M0 M G := by
  obtain ⟨⟨H,hH,le⟩,reg,hn,fr⟩ := h
  exact ⟨H,Nj,hH,by omega,regT_mono reg le,hn,fr⟩

theorem si_of_pxr {M : Mem} {G : GA} (h : PXR n c T Out ko D B Excl H0 M0 M G) (hL : HeapIs G Lo) :
    ∃ Nj', SI n c T Out ko D B Excl Lo Nj' M0 M G ∧ H0.toNat ≤ Lo.toNat := by
  obtain ⟨H,Nj',hH,le,reg,hn,fr⟩ := h
  have e := heapIs_unique hH hL
  subst e
  exact ⟨Nj',⟨⟨H,hH,le_refl _⟩,reg,hn,fr⟩,le⟩

/-- Memory changes confined to words at or above `Lo` keep `SI`. -/
theorem si_mem {M M' : Mem} {G : GA} (h : SI n c T Out ko D B Excl Lo Nj M0 M G)
    (keep : ∀ x, x.toNat < Lo.toNat → M' x = M x) : SI n c T Out ko D B Excl Lo Nj M0 M' G := by
  obtain ⟨hh,reg,hn,fr⟩ := h
  exact ⟨hh,regT_below reg keep,hn,fun x ho hx => (keep x (regT_out_lt reg ho)).trans (fr x ho hx)⟩

/-- A new globals map with a heap pointer at least `Lo` and the same journal counter keeps `SI`. -/
theorem si_glob {M : Mem} {G G' : GA} (h : SI n c T Out ko D B Excl Lo Nj M0 M G)
    (hH : ∃ H : BitVec 64, HeapIs G' H ∧ Lo.toNat ≤ H.toNat)
    (hn : G'.lookup (ofString "journal_n") = some (.val (.word Nj))) : SI n c T Out ko D B Excl Lo Nj M0 M G' :=
  ⟨hH,h.2.1,hn,h.2.2.2⟩

/-- Memory changes at or above `Lo` and in the Keccak state/pad windows keep `SI` (the registry cells, headers and
`ko` arrays and every outside word are off the workspace). -/
theorem si_kp {SP0 FM K Pd NB P0 : BitVec 64} {M M' : Mem} {G : GA}
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (h : SI n c T Out ko D B Excl Lo Nj M0 M G) (keep : ∀ x, x.toNat < Lo.toNat → ¬ KPW K Pd x → M' x = M x) :
    SI n c T Out ko D B Excl Lo Nj M0 M' G := by
  obtain ⟨hh,reg,hn,fr⟩ := h
  refine ⟨hh,regT_keep_except reg (KPW K Pd) keep ?_ ?_,hn,fun x ho hx => ?_⟩
  · intro x hc hk
    rcases hk with hk | hk
    · exact (safe x hc).2.1 hk
    · exact (safe x hc).2.2.1 hk
  · intro Mx lo hdr x hin hk
    rcases hk with hk | hk
    · exact (hkoWs Mx lo hdr x hin).2.1 hk
    · exact (hkoWs Mx lo hdr x hin).2.2.1 hk
  · have hnk : ¬ KPW K Pd x := by
      rintro (hk | hk)
      · exact (hOutSafe x ho).1.2.1 hk
      · exact (hOutSafe x ho).1.2.2.1 hk
    exact (keep x (regT_out_lt reg ho) hnk).trans (fr x ho hx)

end si

section st
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Lo Nj : BitVec 64} {M0 : Mem}

/-- A word store at or above `Lo` keeps `SI`; a normal outcome learns the address is in the domain. -/
theorem aqgd_store_si {LP LQ : GA → Prop} (hw : w.toNat < Lo.toNat) (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧ (D a → LQ s.locals))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y)) :
    AQGD D B A w Vn (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G)
      (fun L M G => LQ L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) RR (.store d v) := by
  intro F s code dom aw sl G hG ⟨lp,si⟩
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,hlo,hq⟩ := hd s aw lp
  have ne : w ≠ a := by intro e; subst e; omega
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · lp)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ⟨by rw [loc]; exact sl,_,by unfold GIs; rw [glob],?_⟩,
    ?_,?_,?_⟩
  · rw [loc]
    exact ⟨hq (dom.2.1 ▸ store_none_dom s d v a ha (hv s · lp) e),
      si_mem si (fun x hx => mem x (fun e => by subst e; omega))⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

#print axioms aqgd_store_si

/-- Two triples on one program with one precondition give the conjunction of their postconditions. -/
theorem aqgd_and {P Q1 Q2 : GA → Mem → GA → Prop} {R1 R2 : ValueHOL 64 → Mem → GA → Prop} {p : ProgHOL 64}
    (h1 : AQGD D B A w Vn P Q1 R1 p) (h2 : AQGD D B A w Vn P Q2 R2 p) :
    AQGD D B A w Vn P (fun L M G => Q1 L M G ∧ Q2 L M G) (fun v M G => R1 v M G ∧ R2 v M G) p := by
  intro F s code dom aw sl H hH pre
  obtain ⟨m,a,n1,r1,c1,b1⟩ := h1 F s code dom aw sl H hH pre
  obtain ⟨_,_,n2,r2,_,_⟩ := h2 F s code dom aw sl H hH pre
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c1,b1⟩
  · obtain ⟨sl1,H1,g1,q1⟩ := n1 e
    obtain ⟨_,H2,g2,q2⟩ := n2 e
    unfold GIs at g1 g2; subst g1 g2
    exact ⟨sl1,_,rfl,q1,q2⟩
  · obtain ⟨H1,g1,q1⟩ := r1 v e
    obtain ⟨H2,g2,q2⟩ := r2 v e
    unfold GIs at g1 g2; subst g1 g2
    exact ⟨_,rfl,q1,q2⟩

#print axioms aqgd_and
end st

section lw
variable {SP0 P0 FM w : BitVec 64} {G0 : GA} {Vn : MlS → Prop}

/-- A heap-aware triple proven with the arena bound raised to the entry heap pointer `Hc` holds at the original bound
from entry heap pointer `Hc`. -/
theorem aqmh_lower {P Q : GA → Mem → BitVec 64 → Prop} {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64}
    {Hc : BitVec 64} (le : P0.toNat ≤ Hc.toNat) (h : AQMH SP0 Hc FM G0 w Vn P Q RR p) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => P L M H ∧ H = Hc) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,e⟩
  subst e
  obtain ⟨awH,_⟩ := aw_raise aw hH
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awH sl H hH pre
  exact ⟨m,fun cont => (aw_lower (a cont) le).1,n,r,c,b⟩

#print axioms aqmh_lower
end lw
end InitECandidate.Runtime
