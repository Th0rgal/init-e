import InitECandidate.Runtime.PtSegMsgGD
/-!
The final phase of the `process_transaction` segment (spine drops 90-97, around the creation-branch `get_account`):
the segment's fresh words `[Lo, Hg)` (`Hg` the heap pointer before the branch) join the outside words of the
registry (`OutX`). Every registry table's arrays lie below its heap pointer (each table is separated from another
one's canonical footprint, which contains all words at or above the heap pointer), and every header lies below it,
so `SI` at `Lo` with heap pointer `Hg` gives `PG` (registry with content at `Hg` against `OutX`); `PG` gives back
`PXR`. Word stores into `[Lo, Hg)` and changes at or above the registry bound or in the Keccak windows keep `PG`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Outside words extended by the fresh segment words `[Lo, Hg)`. -/
def OutX (Out : BitVec 64 → Prop) (Lo Hg : BitVec 64) (x : BitVec 64) : Prop :=
  Out x ∨ (Lo.toNat ≤ x.toNat ∧ x.toNat < Hg.toNat)

/-- Final-phase state: heap pointer at least `Hb`, the registry with content at `Hb` against `OutX Out Lo Hg`, the
journal counter, and the outside words outside `Excl` as in `M0`. -/
def PG (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (Lo Hg Hb Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  (∃ H : BitVec 64, HeapIs G H ∧ Hb.toNat ≤ H.toNat) ∧ RegT n c T (OutX Out Lo Hg) Hb M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M x = M0 x

section pg
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {D : BitVec 64 → Prop} {B : Bool}
  {Excl : BitVec 64 → Prop} {Lo Hg Hb Nj H0 : BitVec 64} {M0 : Mem}

/-- With two distinct tables, every table's arrays lie below the heap pointer. -/
theorem regPure_arr_below {Out' : BitVec 64 → Prop} {H : BitVec 64} {l : Fin n → TLay}
    (pure : RegPure n c T Out' H l) {kA kB : Fin n} (hAB : kA ≠ kB) (j : Fin n) {x : BitVec 64} (hx : (l j).arr x) :
    x.toNat < H.toNat := by
  by_contra hc
  by_cases hj : j = kA
  · subst hj
    exact pure.2.1 kB j (Ne.symm hAB) x (Or.inr (Or.inr hx)) (Or.inr (Or.inr (by omega)))
  · exact pure.2.1 kA j (Ne.symm hj) x (Or.inr (Or.inr hx)) (Or.inr (Or.inr (by omega)))

theorem regT_out_sub {Out' : BitVec 64 → Prop} {H : BitVec 64} {M : Mem} (h : RegT n c T Out' H M D B ko)
    (sub : ∀ x, Out x → Out' x) : RegT n c T Out H M D B ko :=
  let ⟨l,pure,mem,tc,ab⟩ := h; ⟨l,⟨pure.1,pure.2.1,fun x hx => pure.2.2 x (sub x hx)⟩,mem,tc,ab⟩

/-- `SI` at `Lo` with heap pointer `Hg` gives `PG` at `Hg`. -/
theorem pg_of_si {M : Mem} {G : GA} {kA kB : Fin n} (hAB : kA ≠ kB) (h : SI n c T Out ko D B Excl Lo Nj M0 M G)
    (hH : HeapIs G Hg) : PG n c T Out ko D B Excl Lo Hg Hg Nj M0 M G := by
  obtain ⟨⟨H,hH',le⟩,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ := h
  have e := heapIs_unique hH' hH
  subst e
  obtain ⟨tA,sep,o⟩ := regPure_tabs pure mem le
  refine ⟨⟨H,hH,le_refl _⟩,⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,?_⟩,mem,tc,fun x hx => by
    have := ab x hx; omega⟩,hn,fr⟩
  intro x hx i hc
  rcases hx with ho | ⟨lo,hi⟩
  · exact o x ho i hc
  · rcases hc with ⟨h1,h2⟩ | ha | hf
    · have := (pure.1 i).1.hdrP; omega
    · have := regPure_arr_below pure hAB i ha; omega
    · omega

theorem pxr_of_pg {M : Mem} {G : GA} (h0 : H0.toNat ≤ Hb.toNat) (h : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) :
    PXR n c T Out ko D B Excl H0 M0 M G := by
  obtain ⟨⟨H,hH,le⟩,reg,hn,fr⟩ := h
  exact ⟨H,Nj,hH,by omega,regT_mono (regT_out_sub reg (fun x hx => Or.inl hx)) le,hn,fr⟩

theorem pg_glob {M : Mem} {G G' : GA} (h : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G)
    (hH : ∃ H : BitVec 64, HeapIs G' H ∧ Hb.toNat ≤ H.toNat)
    (hn : G'.lookup (ofString "journal_n") = some (.val (.word Nj))) : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G' :=
  ⟨hH,h.2.1,hn,h.2.2.2⟩

/-- Changes at or above `Hb` or in the Keccak windows keep `PG`. -/
theorem pg_kp {SP0 FM K Pd NB P0 : BitVec 64} {M M' : Mem} {G : GA}
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (h : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) (keep : ∀ x, x.toNat < Hb.toNat → ¬ KPW K Pd x → M' x = M x) :
    PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M' G := by
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
    exact (keep x (regT_out_lt reg (Or.inl ho)) hnk).trans (fr x ho hx)

/-- Changes confined to a set `S ⊆ [Lo, Hg)` avoiding the pointer cells and the outside words, plus words at or above
`Hb`, keep `PG`. -/
theorem pg_in {M M' : Mem} {G : GA} (S : BitVec 64 → Prop) (h : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G)
    (hS : ∀ x, S x → (Lo.toNat ≤ x.toNat ∧ x.toNat < Hg.toNat) ∧ (∀ i, x ≠ c i) ∧ ¬ Out x)
    (keep : ∀ x, x.toNat < Hb.toNat → ¬ S x → M' x = M x) : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M' G := by
  classical
  obtain ⟨hh,reg,hn,fr⟩ := h
  let M2 : Mem := fun x => if S x then M' x else M x
  have r2 : RegT n c T (OutX Out Lo Hg) Hb M2 D B ko :=
    regT_frame reg S (fun x hx => ⟨Or.inr (hS x hx).1,(hS x hx).2.1⟩) (fun x hx => by simp [M2,hx])
  refine ⟨hh,regT_below r2 (fun x hx => ?_),hn,fun x ho hx => ?_⟩
  · by_cases hs : S x
    · simp [M2,hs]
    · simp only [M2,hs,if_false]; exact keep x hx hs
  · have hs : ¬ S x := fun hs => (hS x hs).2.2 ho
    exact (keep x (regT_out_lt reg (Or.inl ho)) hs).trans (fr x ho hx)

end pg
end InitECandidate.Runtime
