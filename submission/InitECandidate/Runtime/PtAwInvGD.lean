import InitECandidate.Runtime.PtAwWritersGD
import InitECandidate.Runtime.PtRegSubOGD
/-!
The accounts-written table (`ts + 16`, cell `Ts + 16`) as a ready object beside a registry restricted to the other
tables (`AwIL`): the table is ready (`TabRV`), its cell holds it, the restricted registry treats the cell and the
table's physical region as outside words, and both lie below the heap pointer, off the journal, the key buffer, the
registry cells and the outside words. Kept by any step that keeps the outside words of the restriction off the journal
and the key buffer (`awIL_frame`), and re-established by a content-preserving `jset` on the table (`awIL_jset`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The cell and the physical region of the accounts-written table. -/
def AwFp (Ts Taw : BitVec 64) (la : TLay) (x : BitVec 64) : Prop := x = Ts + 16#64 ∨ TabPhys Taw la x

/-- The accounts-written table with layout `la` beside the restricted registry. -/
def AwIL (m : Nat) (c' T' : Fin m → BitVec 64) (ko' : Fin m) (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop)
    (B : Bool) (J C SKB Ts Taw : BitVec 64) (S : Set (BitVec 64)) (la : TLay) (Hl H : BitVec 64) (M : Mem) : Prop :=
  (TabRV D B Taw la Hl S M ∧ Hl.toNat ≤ H.toNat ∧ M (Ts + 16#64) = .word Taw ∧
    (la.KL = 20 ∨ la.KL = 32 ∨ la.KL = 52) ∧ la.SD.toNat ≤ 56) ∧
  RegT m c' T' (fun x => Out x ∨ AwFp Ts Taw la x) H M D B ko' ∧
  (∀ x, AwFp Ts Taw la x → x.toNat < H.toNat ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x ∧ ∀ i, x ≠ c' i) ∧
  (∀ x, Out x → ¬ TabPhys Taw la x) ∧ ¬ TabPhys Taw la (Ts + 16#64)

section rf
variable {m : Nat} {c' T' : Fin m → BitVec 64} {O O' : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko' : Fin m}

/-- Writes below the heap pointer confined to outside non-cell words, and any writes at or above it, keep the
registry. -/
theorem regT_frame_below {H : BitVec 64} {M M' : Mem} (h : RegT m c' T' O H M D B ko') (S : BitVec 64 → Prop)
    (hS : ∀ x, S x → O x ∧ ∀ i, x ≠ c' i) (keep : ∀ x, x.toNat < H.toNat → ¬ S x → M' x = M x) :
    RegT m c' T' O H M' D B ko' := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T' i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x hx => keep x (regPure_below pure x hx) (fun hs => ?_)),
    tc.frame (pure.1 ko').1.cnt.le (fun x hx => keep x ?_ (fun hs => pure.2.2 x (hS x hs).1 ko' (intabf_canon hx))),
    ab⟩
  · obtain ⟨i,hi⟩ := hx
    rcases hi with rfl | hi
    · exact (hS _ hs).2 i rfl
    · exact pure.2.2 x (hS x hs).1 i (Or.inl hi)
  · rcases hx with hh | ha
    · have := (pure.1 ko').1.hdrP; omega
    · exact ab x ha

/-- The registry at a higher heap pointer with outside words grown by the fresh heap. -/
theorem regT_out_fresh {H H' : BitVec 64} {M : Mem} (h : RegT m c' T' O H M D B ko') {kA kB : Fin m} (hAB : kA ≠ kB)
    (le : H.toNat ≤ H'.toNat) (sub : ∀ x, O' x → O x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) :
    RegT m c' T' O' H' M D B ko' := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  obtain ⟨tA,sep,o⟩ := regPure_tabs pure mem le
  refine ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,fun x hx i hc => ?_⟩,mem,tc,fun x hx => by
    have := ab x hx; omega⟩
  rcases sub x hx with ho | ⟨lo,hi⟩
  · exact o x ho i hc
  · rcases hc with hh | ha | hge
    · have := regPure_below pure x ⟨i,Or.inr hh⟩; omega
    · have := regPure_arr_below pure hAB i ha; omega
    · omega

#print axioms regT_frame_below
#print axioms regT_out_fresh
end rf

section aw
variable {m : Nat} {c' T' : Fin m → BitVec 64} {ko' : Fin m} {Out : BitVec 64 → Prop} {D : BitVec 64 → Prop}
  {B : Bool} {J C SKB Ts Taw : BitVec 64} {S : Set (BitVec 64)}

/-- A step keeping the outside words of the restriction off the journal and the key buffer (and the restricted
registry at a higher heap pointer) keeps the table. -/
theorem awIL_frame {la : TLay} {Hl H H' : BitVec 64} {M M' : Mem}
    (h : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H M)
    (reg' : RegT m c' T' (fun x => Out x ∨ AwFp Ts Taw la x) H' M' D B ko') (le : H.toNat ≤ H'.toNat)
    (keep : ∀ x, (Out x ∨ AwFp Ts Taw la x) → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M x) :
    AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H' M' := by
  obtain ⟨⟨rv,hl,cell,sup,sd⟩,_,sep,oT,cT⟩ := h
  have kA : ∀ x, AwFp Ts Taw la x → M' x = M x := fun x hx =>
    keep x (Or.inr hx) (sep x hx).2.1 (sep x hx).2.2.1
  refine ⟨⟨tabRV_frame rv (fun x hx => kA x (Or.inr hx)),by omega,(kA _ (Or.inl rfl)).trans cell,sup,sd⟩,reg',
    fun x hx => ⟨by have := (sep x hx).1; omega,(sep x hx).2⟩,oT,cT⟩

#print axioms awIL_frame

/-- A content-preserving `jset` on the table re-establishes the invariant at the exit heap pointer, with the exit
layout. -/
theorem awIL_jset {la : TLay} {Hl H0 Nj : BitVec 64} {M0 M' : Mem} {G' : GA} {kA kB : Fin m} (hAB : kA ≠ kB)
    (h : AwIL m c' T' ko' Out D B J C SKB Ts Taw S la Hl H0 M0)
    (hJO : ∀ x, InJ J C x → Out x) (jcell : ∀ x, InJ J C x → ∀ i, x ≠ c' i)
    (jB : J.toNat + C.toNat * 32 ≤ H0.toNat) (skB : ∀ x, SkWin SKB x → x.toNat < H0.toNat)
    (outB : ∀ x, Out x → x.toNat < H0.toNat)
    (js : JSRV D B Taw la S J C Nj H0 M0 M' G') :
    ∃ (la' : TLay) (Hp : BitVec 64), HeapIs G' Hp ∧ H0.toNat ≤ Hp.toNat ∧
      G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧ Nj.toNat < C.toNat ∧
      AwIL m c' T' ko' Out D B J C SKB Ts Taw S la' Hp Hp M' := by
  obtain ⟨⟨rv,hl,cell,sup,sd⟩,reg,sep,oT,cT⟩ := h
  obtain ⟨hlt,hn,⟨Hc,hHc,la',Hp,hHp,hle,rv',eKL,eSD,loc⟩,fr⟩ := js
  have hH : HeapIs G' Hp := hHp
  have hle0 : H0.toNat ≤ Hp.toNat := by omega
  have inJ : ∀ x, InJ J C x → x.toNat < H0.toNat := fun x ⟨_,hi⟩ => by omega
  have cellB := (sep _ (Or.inl rfl)).1
  have reg0 : RegT m c' T' (fun x => Out x ∨ AwFp Ts Taw la x) H0 M' D B ko' :=
    regT_frame_below reg (fun x => InJ J C x ∨ TabPhys Taw la x)
      (fun x hx => by
        rcases hx with hj | ht
        · exact ⟨Or.inl (hJO x hj),jcell x hj⟩
        · exact ⟨Or.inr (Or.inr ht),(sep x (Or.inr ht)).2.2.2⟩)
      (fun x hx hs => fr x hx (fun hj => hs (Or.inl hj)) (fun ht => hs (Or.inr ht)))
  have locF : ∀ x, TabPhys Taw la' x → TabPhys Taw la x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < Hp.toNat) :=
    fun x hx => by
      rcases loc x hx with h | ⟨lo,hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega,hi⟩
  have regP : RegT m c' T' (fun x => Out x ∨ AwFp Ts Taw la' x) Hp M' D B ko' :=
    regT_out_fresh reg0 hAB hle0 (fun x hx => by
      rcases hx with ho | rfl | ht
      · exact Or.inl (Or.inl ho)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · rcases locF x ht with h | h
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h)
  have cellK : M' (Ts + 16#64) = .word Taw :=
    (fr _ cellB (sep _ (Or.inl rfl)).2.1 cT).trans cell
  refine ⟨la',Hp,hH,hle0,hn,hlt,⟨rv',le_refl _,cellK,by rw [eKL]; exact sup,by rw [eSD]; exact sd⟩,regP,
    fun x hx => ?_,fun x ho ht => ?_,fun ht => ?_⟩
  · rcases hx with rfl | ht
    · exact ⟨by omega,(sep _ (Or.inl rfl)).2⟩
    · rcases locF x ht with h | ⟨lo,hi⟩
      · have s := sep x (Or.inr h)
        exact ⟨by omega,s.2⟩
      · refine ⟨hi,fun hj => ?_,fun hs => ?_,fun i hc => ?_⟩
        · have := inJ x hj; omega
        · have := skB x hs; omega
        · obtain ⟨_,pure0,_⟩ := reg0
          have := regPure_below pure0 x ⟨i,Or.inl hc⟩; omega
  · rcases locF x ht with h | ⟨lo,_⟩
    · exact oT x ho h
    · have := outB x ho; omega
  · rcases locF _ ht with h | ⟨lo,_⟩
    · exact cT h
    · omega

#print axioms awIL_jset
end aw
end InitECandidate.Runtime
