import InitECandidate.Runtime.PtAwExtGD
import InitECandidate.Runtime.PtAwDestroyGD
/-!
The accounts-written table (`ts + 16`) as a registry-free side condition (`AwC`, `AwR`): ready, its cell holding it, its
cell and region below the heap pointer, off the journal, the key buffer and the outside words. With the whole registry
(the table at index `k16`, cell `Ts + 16`) it gives the restricted invariant `AwIL` used by the writer content lemmas
(`awIL_of_full`), and every writer exit (`AwPost`) gives it back (`awR_of_awPost`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The accounts-written table, ready with layout `la`, below the heap pointer `H`. -/
def AwC (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop) (B : Bool) (J C SKB Ts Taw : BitVec 64) (la : TLay)
    (Hl H : BitVec 64) (M : Mem) : Prop :=
  (TabRV D B Taw la Hl Set.univ M ∧ Hl.toNat ≤ H.toNat ∧ M (Ts + 16#64) = .word Taw ∧
    (la.KL = 20 ∨ la.KL = 32 ∨ la.KL = 52) ∧ la.SD.toNat ≤ 56) ∧
  (∀ x, AwFp Ts Taw la x → x.toNat < H.toNat ∧ ¬ InJ J C x ∧ ¬ SkWin SKB x) ∧
  (∀ x, Out x → ¬ TabPhys Taw la x) ∧ ¬ TabPhys Taw la (Ts + 16#64)

/-- The side condition over memory and globals: the table ready at the current heap pointer. -/
def AwR (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop) (B : Bool) (J C SKB Ts Taw : BitVec 64) (M : Mem) (G : GA) :
    Prop :=
  ∃ (la : TLay) (Hl H : BitVec 64), HeapIs G H ∧ AwC Out D B J C SKB Ts Taw la Hl H M

section cv
variable {n m : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {D : BitVec 64 → Prop} {B : Bool}
  {ko k16 : Fin n} {e : Fin m → Fin n} {ko' : Fin m} {J C SKB Ts Taw : BitVec 64}

theorem regT_outSubR {O O' : BitVec 64 → Prop} {H : BitVec 64} {M : Mem} {k : Fin m} {c' T' : Fin m → BitVec 64}
    (h : RegT m c' T' O H M D B k) (sub : ∀ x, O' x → O x) : RegT m c' T' O' H M D B k := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  exact ⟨l,⟨pure.1,pure.2.1,fun x hx i => pure.2.2 x (sub x hx) i⟩,mem,tc,ab⟩

/-- The restricted invariant from the whole registry and the side condition. -/
theorem awIL_of_full (inj : ∀ i j, e i = e j → i = j) (hko : e ko' = ko)
    (hne : ∀ i, e i ≠ k16) (hc16 : c k16 = Ts + 16#64) {la : TLay} {Hl H : BitVec 64} {M : Mem}
    (reg : RegT n c T Out H M D B ko) (aw : AwC Out D B J C SKB Ts Taw la Hl H M) :
    AwIL m (fun i => c (e i)) (fun i => T (e i)) ko' Out D B J C SKB Ts Taw Set.univ la Hl H M := by
  obtain ⟨⟨rv,hl,cell,sup,sd⟩,sep,oT,cT⟩ := aw
  have reg0 := reg
  obtain ⟨l,pure,mem,_,_⟩ := reg0
  obtain ⟨_,lhd,_⟩ := tabAt_of_tabRV rv hl
  have hT : T k16 = Taw := by
    have h1 := (mem k16).1; rw [hc16,cell] at h1
    simp only [HolWordLab.word.injEq] at h1; exact h1.symm
  have hdrE := hdr_unique lhd (by rw [← hT]; exact (mem k16).2)
  obtain ⟨_,e1,e2,_,e4,e5,e6,e7,e8⟩ := hdrE
  have arrE : ∀ x, (l k16).arr x ↔ la.arr x := fun x => by
    show ArrOf _ _ _ _ _ _ _ x ↔ ArrOf _ _ _ _ _ _ _ x
    rw [e1,e2,e4,e5,e6,e7,e8]
  have rs := regT_restrict_out inj hko reg
  refine ⟨⟨rv,hl,cell,sup,sd⟩,regT_outSubR rs (fun x hx => ?_),fun x hx => ⟨(sep x hx).1,(sep x hx).2.1,
    (sep x hx).2.2,fun i hc => ?_⟩,oT,cT⟩
  · rcases hx with ho | hfp
    · exact Or.inl ho
    · refine Or.inr ⟨k16,fun i h => hne i h,?_⟩
      rcases hfp with rfl | hph
      · exact Or.inl hc16.symm
      · rcases hph with hh | ha
        · exact Or.inr (Or.inl (by rw [hT]; exact hh))
        · exact Or.inr (Or.inr ⟨_,_,_,_,_,_,_,_,_,(mem k16).2,(arrE x).2 ha⟩)
  · have ne : e i ≠ k16 := hne i
    rcases hx with rfl | hph
    · exact cell_ne pure mem ne (hc.symm.trans hc16.symm) |>.elim
    · subst hc
      have hc' : (l k16).canon (T k16) H (c (e i)) := by
        rcases hph with hh | ha
        · exact Or.inl (by rw [hT]; exact hh)
        · exact Or.inr (Or.inl ((arrE _).2 ha))
      exact pure.2.1 k16 (e i) (Ne.symm ne) _ (Or.inl rfl) hc'

#print axioms regT_outSubR
#print axioms awIL_of_full

/-- A writer exit gives the side condition back. -/
theorem awR_of_awPost {H0 : BitVec 64} {M : Mem} {G : GA}
    (h : AwPost m (fun i => c (e i)) (fun i => T (e i)) ko' Out D B J C SKB Ts Taw Set.univ H0 M G) :
    AwR Out D B J C SKB Ts Taw M G := by
  obtain ⟨la,Hp,_,hH,_,_,⟨rv,hl,cell,sup,sd⟩,_,sep,oT,cT⟩ := h
  exact ⟨la,Hp,Hp,hH,⟨rv,hl,cell,sup,sd⟩,fun x hx => ⟨(sep x hx).1,(sep x hx).2.1,(sep x hx).2.2.1⟩,oT,cT⟩

#print axioms awR_of_awPost
end cv
end InitECandidate.Runtime
