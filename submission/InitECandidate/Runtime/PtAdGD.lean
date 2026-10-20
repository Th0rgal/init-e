import InitECandidate.Runtime.PtNewRVGD
/-!
Block-access-list account records (`ad`, 40 bytes): `AdO D B O ad H M` says the record words `ad, ad+8, …, ad+32`
hold the storage-write table `t0` (ready, values in its set `Ls` of 40-byte lists), the storage-read table `t8`
(`TabO`), and the balance/nonce/code lists (element sizes 40/16/24); every component (record words, `t0`'s physical
region, `t8`, the three lists, each list of `Ls`) has its own region inside `O`, the regions pairwise disjoint.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Components of an account record. -/
inductive AdC where
  | recw | t0 | t8 | l16 | l24 | l32 | lst (l : BitVec 64)
  deriving DecidableEq

/-- Live components (the storage-write lists only for `l ∈ Ls`). -/
def AdC.live (Ls : Set (BitVec 64)) : AdC → Prop
  | .lst l => l ∈ Ls
  | _ => True

/-- The five record words. -/
def RecW (ad x : BitVec 64) : Prop :=
  x = ad ∨ x = ad + 8#64 ∨ x = ad + 16#64 ∨ x = ad + 24#64 ∨ x = ad + 32#64

/-- Pairwise disjoint live regions. -/
def RgDis {κ : Type} (live : κ → Prop) (Rg : κ → BitVec 64 → Prop) : Prop :=
  ∀ c c', live c → live c' → c ≠ c' → ∀ x, Rg c x → ¬ Rg c' x

/-- A valid account record owned by `O`. -/
def AdO (D : BitVec 64 → Prop) (B : Bool) (O : BitVec 64 → Prop) (ad H : BitVec 64) (M : Mem) : Prop :=
  ∃ (t0 t8 l16 l24 l32 : BitVec 64) (Ls : Set (BitVec 64)) (Rg : AdC → BitVec 64 → Prop) (l0 : TLay)
    (Hl0 : BitVec 64),
    (M ad = .word t0 ∧ M (ad + 8#64) = .word t8 ∧ M (ad + 16#64) = .word l16 ∧ M (ad + 24#64) = .word l24 ∧
      M (ad + 32#64) = .word l32) ∧ (∀ x, RecW ad x → Rg .recw x) ∧
    (TabRV D B t0 l0 Hl0 Ls M ∧ Hl0.toNat ≤ H.toNat ∧ l0.KL = 32#64 ∧ l0.SD.toNat ≤ 56 ∧
      ∀ x, TabPhys t0 l0 x → Rg .t0 x) ∧
    TabO (Rg .t8) t8 H M ∧ LstO 40#64 (Rg .l16) l16 M ∧ LstO 16#64 (Rg .l24) l24 M ∧ LstO 24#64 (Rg .l32) l32 M ∧
    (∀ l ∈ Ls, LstO 40#64 (Rg (.lst l)) l M) ∧ RgDis (AdC.live Ls) Rg ∧
    ∀ c, AdC.live Ls c → ∀ x, Rg c x → O x

section ad
variable {D : BitVec 64 → Prop} {B : Bool} {O O' : BitVec 64 → Prop} {ad H : BitVec 64} {M M' : Mem}

theorem adO_sub (h : AdO D B O ad H M) (sub : ∀ x, O x → O' x) : AdO D B O' ad H M := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,cells,hrw,tr,tO,a,b,c,ls,dis,inO⟩ := h
  exact ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,cells,hrw,tr,tO,a,b,c,ls,dis,fun c hc x hx => sub x (inO c hc x hx)⟩

theorem adO_mono {H' : BitVec 64} (h : AdO D B O ad H M) (le : H.toNat ≤ H'.toNat) : AdO D B O ad H' M := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,cells,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := h
  exact ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,cells,hrw,⟨rv,by omega,kl,sd,ph⟩,tabO_mono tO le,a,b,c,ls,dis,inO⟩

theorem adO_frame (h : AdO D B O ad H M) (keep : ∀ x, O x → M' x = M x) : AdO D B O ad H M' := by
  obtain ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,⟨c0,c8,c16,c24,c32⟩,hrw,⟨rv,hl,kl,sd,ph⟩,tO,a,b,c,ls,dis,inO⟩ := h
  have k : ∀ cc, AdC.live Ls cc → ∀ x, Rg cc x → M' x = M x := fun cc hc x hx => keep x (inO cc hc x hx)
  have kr : ∀ x, RecW ad x → M' x = M x := fun x hx => k .recw trivial x (hrw x hx)
  refine ⟨t0,t8,l16,l24,l32,Ls,Rg,l0,Hl0,⟨?_,?_,?_,?_,?_⟩,hrw,⟨tabRV_frame rv (fun x hx => k .t0 trivial x (ph x hx)),
    hl,kl,sd,ph⟩,tabO_frame tO (k .t8 trivial),lstO_frame a (k .l16 trivial),lstO_frame b (k .l24 trivial),
    lstO_frame c (k .l32 trivial),fun l hl => lstO_frame (ls l hl) (k (.lst l) hl),dis,inO⟩
  · rw [kr _ (Or.inl rfl)]; exact c0
  · rw [kr _ (Or.inr (Or.inl rfl))]; exact c8
  · rw [kr _ (Or.inr (Or.inr (Or.inl rfl)))]; exact c16
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact c24
  · rw [kr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact c32

#print axioms adO_frame
end ad
end InitECandidate.Runtime
