import InitECandidate.Runtime.RecFrameGD
import InitECandidate.Runtime.PtKoWsLGD
/-!
`RecC` in frame form (`recoverSender_frame`: the actual `recover_sender_with_chain_id` keeps every word below its entry
heap pointer outside `RWin` = sender, Keccak state/pad, accelerator scratch), the scratch-pinned process arena
`JWSBUS` and its converter, and registry/window helpers for the call-site composition.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString


section rf
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}
  {DF : Nat}


end rf


section cv
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {SP0 P0 FM J C SKB Bo U Sc Nj : BitVec 64}
  {G0 : GA}


end cv

section rk
variable {D : BitVec 64 → Prop} {B : Bool}

/-- The registry with content at heap pointer `H` survives memory changes confined to words at or above `H` and to a
set `W` avoiding its pointer cells, headers and the `ko` arrays. -/
theorem regT_keep_exceptL {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (W : BitVec 64 → Prop)
    (keep : ∀ x, x.toNat < H.toNat → ¬ W x → M' x = M x)
    (hcell : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → ¬ W x)
    (hko : TabAvoid (fun x => ¬ W x) (T ko)) :
    RegT n c T Out H M' D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x ?_ (hcell x ⟨i,hx⟩)),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x ?_ (hko (l ko) _ (pure.1 ko).1 x hx)),ab⟩
  · rcases hx with rfl | ⟨_,hi⟩
    · by_contra hc
      exact (pure.1 i).2 (Or.inr (Or.inr (by omega)))
    · have := (pure.1 i).1.hdrP; omega
  · rcases hx with ⟨_,hi⟩ | h | h | h | h | h
    · have := (pure.1 ko).1.hdrP; omega
    · exact ab x (Or.inl h)
    · exact ab x (Or.inr (Or.inl h))
    · exact ab x (Or.inr (Or.inr (Or.inl h)))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inr h))))

#print axioms regT_keep_exceptL
end rk


end InitECandidate.Runtime
