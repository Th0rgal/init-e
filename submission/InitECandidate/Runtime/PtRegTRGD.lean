import InitECandidate.Runtime.PtTabOSetGD
/-!
The content-carrying registry with an owned region (`RegTR`): `RegT` plus a region `Rr` containing every registry
pointer cell, header and array. It survives writes outside `Rr` and heap growth; a set on a registry table other
than the content table re-establishes it at the exit heap with the region grown by the fresh heap, changing memory
below the entry heap only inside `Rr`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The content-carrying registry with all cells, headers and arrays in `Rr`. -/
def RegTR (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (H : BitVec 64) (M : Mem)
    (D : BitVec 64 → Prop) (B : Bool) (ko : Fin n) (Rr : BitVec 64 → Prop) : Prop :=
  ∃ l : Fin n → TLay, RegPure n c T Out H l ∧ RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧
    (∀ x, (l ko).arr x → x.toNat < H.toNat) ∧ ∀ i x, (x = c i ∨ HdrR (T i) x ∨ (l i).arr x) → Rr x

section rr
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
  {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} {Rr Rr' : BitVec 64 → Prop}

theorem regTR_regT (h : RegTR n c T Out H M D B ko Rr) : RegT n c T Out H M D B ko :=
  let ⟨l,pure,mem,tc,ab,_⟩ := h; ⟨l,pure,mem,tc,ab⟩

theorem regTR_sub (h : RegTR n c T Out H M D B ko Rr) (sub : ∀ x, Rr x → Rr' x) : RegTR n c T Out H M D B ko Rr' :=
  let ⟨l,pure,mem,tc,ab,rr⟩ := h; ⟨l,pure,mem,tc,ab,fun i x hx => sub x (rr i x hx)⟩

theorem regTR_mono {H' : BitVec 64} (h : RegTR n c T Out H M D B ko Rr) (le : H.toNat ≤ H'.toNat) :
    RegTR n c T Out H' M D B ko Rr := by
  obtain ⟨l,pure,mem,tc,ab,rr⟩ := h
  obtain ⟨tA,sep,o⟩ := regPure_tabs pure mem le
  exact ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,mem,tc,fun x hx => by have := ab x hx; omega,rr⟩

theorem regTR_frame (h : RegTR n c T Out H M D B ko Rr) (keep : ∀ x, Rr x → M' x = M x) :
    RegTR n c T Out H M' D B ko Rr := by
  obtain ⟨l,pure,mem,tc,ab,rr⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x (rr i x (by
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)))),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x (rr ko x (by
      rcases hx with h | h | h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))),ab,rr⟩

/-- Two headers of the same table in one memory agree on all fields. -/
theorem hdr_unique {M : Mem} {Tt KL SD C N KS VS US OS OPS KL' SD' C' N' KS' VS' US' OS' OPS' : BitVec 64}
    (h : Hdr M Tt KL SD C N KS VS US OS OPS) (h' : Hdr M Tt KL' SD' C' N' KS' VS' US' OS' OPS') :
    KL' = KL ∧ SD' = SD ∧ C' = C ∧ N' = N ∧ KS' = KS ∧ VS' = VS ∧ US' = US ∧ OS' = OS ∧ OPS' = OPS := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8⟩ := h
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8⟩ := h'
  rw [a0] at b0; rw [a1] at b1; rw [a2] at b2; rw [a3] at b3; rw [a4] at b4; rw [a5] at b5; rw [a6] at b6
  rw [a7] at b7; rw [a8] at b8
  simp only [HolWordLab.word.injEq] at b0 b1 b2 b3 b4 b5 b6 b7 b8
  exact ⟨b0.symm,b1.symm,b2.symm,b3.symm,b4.symm,b5.symm,b6.symm,b7.symm,b8.symm⟩

/-- A set on registry table `kd ≠ ko`: the registry with region grown by the fresh heap at the exit heap; memory
below the entry heap changed only inside `Rr`. -/
theorem regTR_set {H' : BitVec 64} {kd : Fin n} (ne : kd ≠ ko) (l : Fin n → TLay) (pure : RegPure n c T Out H l)
    (mem : RegMem n c T l M) (tc : TCont D B M (T ko) (l ko)) (ab : ∀ x, (l ko).arr x → x.toNat < H.toNat)
    (rr : ∀ i x, (x = c i ∨ HdrR (T i) x ∨ (l i).arr x) → Rr x)
    (post : SetPost (T kd) ((l kd).canon (T kd) H) M (l kd).C (l kd).SD (l kd).KS (l kd).VS (l kd).US (l kd).OS
      (l kd).OPS H M' H') :
    RegTR n c T Out H' M' D B ko (fun x => Rr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧ H.toNat ≤ H'.toNat ∧
      ∀ x, x.toNat < H.toNat → ¬ Rr x → M' x = M x := by
  have reg := regT_set ne l pure mem tc ab post
  obtain ⟨l',pure',mem',agree⟩ := reg_set_keep l (reg_of pure mem) pure.2.1 pure.2.2 kd post
  obtain ⟨le,fr,KL',SD',C',N',KS',VS',US',OS',OPS',b',_,hd',li'⟩ := post
  have frX : ∀ x, x.toNat < H.toNat → ¬ Rr x → M' x = M x := fun x hx hr => fr x (fun hc => by
    rcases hc with h | h | h
    · exact hr (rr kd x (Or.inr (Or.inl h)))
    · exact hr (rr kd x (Or.inr (Or.inr h)))
    · omega)
  obtain ⟨l2,pure2,mem2,tc2,ab2⟩ := reg
  refine ⟨⟨l2,pure2,mem2,tc2,ab2,fun i x hx => ?_⟩,le,frX⟩
  rcases hx with h | h | h
  · exact Or.inl (rr i x (Or.inl h))
  · exact Or.inl (rr i x (Or.inr (Or.inl h)))
  · by_cases e : i = kd
    · subst e
      obtain ⟨_,_,eC,_,eKS,eVS,eUS,eOS,eOPS⟩ := hdr_unique hd' (mem2 i).2
      have eSD : (l2 i).SD = SD' := (hdr_unique hd' (mem2 i).2).2.1
      unfold TLay.arr at h
      rw [eC,eSD,eKS,eVS,eUS,eOS,eOPS] at h
      rcases li' x h with h | h
      · exact Or.inl (rr i x (Or.inr (Or.inr h)))
      · exact Or.inr h
    · have hdrs := hdr_unique (mem' i).2 (mem2 i).2
      rw [agree i e] at hdrs
      obtain ⟨_,eSD,eC,_,eKS,eVS,eUS,eOS,eOPS⟩ := hdrs
      unfold TLay.arr at h
      rw [eC,eSD,eKS,eVS,eUS,eOS,eOPS] at h
      exact Or.inl (rr i x (Or.inr (Or.inr h)))

#print axioms regTR_set
end rr
end InitECandidate.Runtime
