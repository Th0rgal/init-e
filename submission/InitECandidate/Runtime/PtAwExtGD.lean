import InitECandidate.Runtime.PtAwInvGD
/-!
Re-extension of the registry restricted to the tables other than the accounts-written table (`AwIL`) to the whole
registry, with the accounts-written table at the layout of its ready-table invariant (`regT_extend_aw`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ta
variable {D : BitVec 64 → Prop} {B : Bool}

/-- A ready table is laid out against its canonical footprint at any heap pointer above its frontier bound, with its
header in memory and its physical region below. -/
theorem tabAt_of_tabRV {Tt Hl H : BitVec 64} {la : TLay} {S : Set (BitVec 64)} {M : Mem}
    (rv : TabRV D B Tt la Hl S M) (le : Hl.toNat ≤ H.toNat) :
    la.ok Tt H ∧ la.hdr M Tt ∧ ∀ x, TabPhys Tt la x → x.toNat < H.toNat := by
  obtain ⟨F,s,Pt,hm,_,_,_,hP,_,hT,rd,_⟩ := rv
  obtain ⟨lay,hd,lt⟩ := ready_hlay rd hT
  refine ⟨hlay_canon lay (by omega),by rw [← hm]; exact hd,fun x hx => by have := lt x hx; omega⟩

#print axioms tabAt_of_tabRV
end ta

section ex
variable {n m : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko k16 : Fin n} {e : Fin m → Fin n} {ko' : Fin m} {J C SKB Ts Taw : BitVec 64} {S : Set (BitVec 64)}

/-- The whole registry from the restriction and the ready accounts-written table (its cell `c k16`). -/
theorem regT_extend_aw (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko) (cov : ∀ j, j ≠ k16 → ∃ i, e i = j)
    (hne : ∀ i, e i ≠ k16) {kA kB : Fin m} (hAB : kA ≠ kB) (hc16 : c k16 = Ts + 16#64) (hT16 : T k16 = Taw)
    {la : TLay} {Hl H : BitVec 64} {M : Mem}
    (aw : AwIL m (fun i => c (e i)) (fun i => T (e i)) ko' Out D B J C SKB Ts Taw S la Hl H M) :
    RegT n c T Out H M D B ko := by
  obtain ⟨⟨rv,hl,cell,_,_⟩,reg',sep,oT,cT⟩ := aw
  obtain ⟨lok,lhd,lbelow⟩ := tabAt_of_tabRV rv hl
  obtain ⟨l',pure',mem',tc',ab'⟩ := reg'
  let L : Fin n → TLay := fun j => if h : ∃ i, e i = j then l' (Classical.choose h) else la
  have Lsub : ∀ i, L (e i) = l' i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i,rfl⟩
    show (if h : ∃ i', e i' = e i then l' (Classical.choose h) else la) = l' i
    rw [dif_pos h,inj _ _ (Classical.choose_spec h)]
  have L16 : L k16 = la := by
    show (if h : ∃ i, e i = k16 then l' (Classical.choose h) else la) = la
    rw [dif_neg (fun ⟨i,h⟩ => hne i h)]
  have cases : ∀ j, (∃ i, e i = j) ∨ j = k16 := fun j => by
    by_cases h : j = k16
    · exact Or.inr h
    · exact Or.inl (cov j h)
  have awFp : ∀ x, (x = c k16 ∨ HdrR (T k16) x ∨ (L k16).arr x) → AwFp Ts Taw la x := fun x hx => by
    rw [L16,hc16,hT16] at hx
    rcases hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have subB : ∀ i x, (x = c (e i) ∨ HdrR (T (e i)) x ∨ (l' i).arr x) → x.toNat < H.toNat := fun i x hx => by
    rcases hx with h | h | h
    · exact regPure_below pure' x ⟨i,Or.inl h⟩
    · exact regPure_below pure' x ⟨i,Or.inr h⟩
    · exact regPure_arr_below pure' hAB i h
  refine ⟨L,⟨fun j => ?_,fun j1 j2 ne => ?_,fun x hx j => ?_⟩,fun j => ?_,?_,?_⟩
  · rcases cases j with ⟨i,rfl⟩ | rfl
    · rw [Lsub]; exact pure'.1 i
    · rw [L16,hT16]
      refine ⟨lok,fun hc => ?_⟩
      rw [hc16] at hc
      rcases hc with hh | ha | hge
      · exact cT (Or.inl hh)
      · exact cT (Or.inr ha)
      · have := (sep _ (Or.inl rfl)).1; omega
  · rcases cases j1 with ⟨i1,rfl⟩ | rfl <;> rcases cases j2 with ⟨i2,rfl⟩ | rfl
    · rw [Lsub,Lsub]; exact pure'.2.1 i1 i2 (fun h => ne (congrArg e h))
    · rw [Lsub]
      exact fun x hx hc => pure'.2.2 x (Or.inr (awFp x hx)) i1 hc
    · rw [L16,Lsub,hT16]
      intro x hx hc
      have hlt := subB i2 x hx
      rcases hc with hh | ha | hge
      · rcases hx with hce | hh2 | ha2
        · exact (sep x (Or.inr (Or.inl hh))).2.2.2 i2 hce
        · exact pure'.2.2 x (Or.inr (Or.inr (Or.inl hh))) i2 (Or.inl hh2)
        · exact pure'.2.2 x (Or.inr (Or.inr (Or.inl hh))) i2 (Or.inr (Or.inl ha2))
      · rcases hx with hce | hh2 | ha2
        · exact (sep x (Or.inr (Or.inr ha))).2.2.2 i2 hce
        · exact pure'.2.2 x (Or.inr (Or.inr (Or.inr ha))) i2 (Or.inl hh2)
        · exact pure'.2.2 x (Or.inr (Or.inr (Or.inr ha))) i2 (Or.inr (Or.inl ha2))
      · omega
    · exact absurd rfl ne
  · rcases cases j with ⟨i,rfl⟩ | rfl
    · rw [Lsub]; exact pure'.2.2 x (Or.inl hx) i
    · rw [L16,hT16]
      intro hc
      rcases hc with hh | ha | hge
      · exact oT x hx (Or.inl hh)
      · exact oT x hx (Or.inr ha)
      · exact pure'.2.2 x (Or.inl hx) kA (Or.inr (Or.inr hge))
  · rcases cases j with ⟨i,rfl⟩ | rfl
    · rw [Lsub]; exact mem' i
    · rw [L16,hc16,hT16]; exact ⟨cell,lhd⟩
  · rw [← hko,Lsub]; exact tc'
  · rw [← hko,Lsub]; exact ab'

#print axioms regT_extend_aw

end ex
end InitECandidate.Runtime
