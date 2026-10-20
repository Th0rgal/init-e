import InitECandidate.Runtime.PtIncorpGD
/-!
The registry region read off memory (`RegRgM`): pointer cells, headers, and the arrays described by the headers in
memory. A content-carrying registry is a registry with this region (`regTR_of_regT`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The registry region read off memory. -/
def RegRgM (n : Nat) (c T : Fin n → BitVec 64) (M : Mem) (x : BitVec 64) : Prop :=
  ∃ i, x = c i ∨ HdrR (T i) x ∨ ∃ KL SD C N KS VS US OS OPS : BitVec 64, Hdr M (T i) KL SD C N KS VS US OS OPS ∧
    ArrOf C SD KS VS US OS OPS x

theorem regTR_of_regT {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} (h : RegT n c T Out H M D B ko) :
    RegTR n c T Out H M D B ko (RegRgM n c T M) := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  refine ⟨l,pure,mem,tc,ab,fun i x hx => ⟨i,?_⟩⟩
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨_,_,_,_,_,_,_,_,_,(mem i).2,h⟩)

#print axioms regTR_of_regT

/-- The memory-read registry region of the registry at the heap lies below the heap. -/
theorem regRgM_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} (h : RegT n c T Out H M D B ko) {kA kB : Fin n} (hAB : kA ≠ kB) :
    ∀ x, RegRgM n c T M x → x.toNat < H.toNat := by
  obtain ⟨l,pure,mem,_,_⟩ := h
  intro x ⟨i,hx⟩
  have lay := (pure.1 i).1
  rcases hx with rfl | hx | ⟨KL,SD,C,N,KS,VS,US,OS,OPS,hd,ha⟩
  · by_contra hc
    exact (pure.1 i).2 (Or.inr (Or.inr (by omega)))
  · have := lay.hdrP; obtain ⟨_,h2⟩ := hx; omega
  · obtain ⟨_,_,eC,_,eKS,eVS,eUS,eOS,eOPS⟩ := hdr_unique (mem i).2 hd
    have eSD := (hdr_unique (mem i).2 hd).2.1
    subst eC eKS eVS eUS eOS eOPS eSD
    exact regPure_arr_below pure hAB i ha

#print axioms regRgM_below
end InitECandidate.Runtime
