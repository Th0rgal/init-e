import InitECandidate.Runtime.PtAdGD
/-!
The block-access-list state: components `ba` (`bal_accounts`, ready, key length 20, values the live account records),
`ia`/`is` (`bal_idx_accts`/`bal_idx_stor`, `TabO`), `kb` (the 64-byte `bal_key_buf`) and one account record per live
address (`AdO`). `BalW` says every live component is valid in its own region, the regions pairwise disjoint and below
the heap pointer. `balW_upd`: an operation on one component confined to its region and fresh heap keeps the state with
that region grown.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive BalK where
  | ba | ia | is | kb | ad (a : BitVec 64)
  deriving DecidableEq

def BalK.live (ADs : Set (BitVec 64)) : BalK → Prop
  | .ad a => a ∈ ADs
  | _ => True

/-- Validity of one component in its region `O` at heap pointer `H`. -/
def BalV (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB : BitVec 64) (ADs : Set (BitVec 64)) :
    BalK → (BitVec 64 → Prop) → BitVec 64 → Mem → Prop
  | .ba, O, H, M => ∃ (lba : TLay) (Hl : BitVec 64), TabRV D B BA lba Hl ADs M ∧ Hl.toNat ≤ H.toNat ∧
      lba.KL = 20#64 ∧ lba.SD.toNat ≤ 56 ∧ ∀ x, TabPhys BA lba x → O x
  | .ia, O, H, M => TabO O IA H M
  | .is, O, H, M => TabO O IS H M
  | .kb, O, _, _ => KB.toNat % 8 = 0 ∧ ∀ x : BitVec 64, KB.toNat ≤ x.toNat → x.toNat < KB.toNat + 64 → O x
  | .ad a, O, H, M => AdO D B O a H M

/-- The block-access-list state with explicit live accounts and regions. -/
def BalW (D : BitVec 64 → Prop) (B : Bool) (BA IA IS KB : BitVec 64) (ADs : Set (BitVec 64))
    (Rg : BalK → BitVec 64 → Prop) (H : BitVec 64) (M : Mem) : Prop :=
  (∀ c, BalK.live ADs c → BalV D B BA IA IS KB ADs c (Rg c) H M) ∧ RgDis (BalK.live ADs) Rg ∧
    ∀ c, BalK.live ADs c → ∀ x, Rg c x → x.toNat < H.toNat

section bv
variable {D : BitVec 64 → Prop} {B : Bool} {BA IA IS KB : BitVec 64} {ADs : Set (BitVec 64)}
  {O O' : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}

theorem balV_frame (c : BalK) (h : BalV D B BA IA IS KB ADs c O H M) (keep : ∀ x, O x → M' x = M x) :
    BalV D B BA IA IS KB ADs c O H M' := by
  cases c with
  | ba => obtain ⟨l,Hl,rv,a,b,d,e⟩ := h; exact ⟨l,Hl,tabRV_frame rv (fun x hx => keep x (e x hx)),a,b,d,e⟩
  | ia => exact tabO_frame h keep
  | is => exact tabO_frame h keep
  | kb => exact h
  | ad a => exact adO_frame h keep

theorem balV_mono (c : BalK) {H' : BitVec 64} (h : BalV D B BA IA IS KB ADs c O H M) (le : H.toNat ≤ H'.toNat) :
    BalV D B BA IA IS KB ADs c O H' M := by
  cases c with
  | ba => obtain ⟨l,Hl,rv,a,b,d,e⟩ := h; exact ⟨l,Hl,rv,by omega,b,d,e⟩
  | ia => exact tabO_mono h le
  | is => exact tabO_mono h le
  | kb => exact h
  | ad a => exact adO_mono h le

theorem balV_sub (c : BalK) (h : BalV D B BA IA IS KB ADs c O H M) (sub : ∀ x, O x → O' x) :
    BalV D B BA IA IS KB ADs c O' H M := by
  cases c with
  | ba => obtain ⟨l,Hl,rv,a,b,d,e⟩ := h; exact ⟨l,Hl,rv,a,b,d,fun x hx => sub x (e x hx)⟩
  | ia => exact tabO_sub h sub
  | is => exact tabO_sub h sub
  | kb => exact ⟨h.1,fun x a b => sub x (h.2 x a b)⟩
  | ad a => exact adO_sub h sub

theorem balV_values {ADs' : Set (BitVec 64)} (c : BalK) (h : BalV D B BA IA IS KB ADs c O H M) (sub : ADs ⊆ ADs') :
    BalV D B BA IA IS KB ADs' c O H M := by
  cases c with
  | ba => obtain ⟨l,Hl,rv,a,b,d,e⟩ := h; exact ⟨l,Hl,tabRV_mono rv (le_refl _) sub,a,b,d,e⟩
  | ia => exact h
  | is => exact h
  | kb => exact h
  | ad a => exact h

/-- An operation on the live component `c` confined to its region and the fresh heap `[H, H')`. -/
theorem balW_upd {Rg : BalK → BitVec 64 → Prop} {H' : BitVec 64} (c : BalK) (hc : BalK.live ADs c)
    (m : BalW D B BA IA IS KB ADs Rg H M) (le : H.toNat ≤ H'.toNat)
    (new : BalV D B BA IA IS KB ADs c (fun x => Rg c x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) H' M')
    (fr : ∀ x, x.toNat < H.toNat → ¬ Rg c x → M' x = M x) :
    BalW D B BA IA IS KB ADs (fun c' x => Rg c' x ∨ (c' = c ∧ H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) H' M' := by
  obtain ⟨v,dis,bl⟩ := m
  refine ⟨fun c' hc' => ?_,fun c1 c2 h1 h2 ne x hx1 hx2 => ?_,fun c' hc' x hx => ?_⟩
  · by_cases e : c' = c
    · subst e
      exact balV_sub c' new (fun x h => by
        rcases h with h | ⟨h1,h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl,h1,h2⟩)
    · exact balV_sub c' (balV_mono c' (balV_frame c' (v c' hc') (fun x hx => fr x (bl c' hc' x hx)
        (fun h => dis c' c hc' hc e x hx h))) le) (fun x h => Or.inl h)
  · rcases hx1 with h | ⟨e1,a1,_⟩ <;> rcases hx2 with h' | ⟨e2,a2,_⟩
    · exact dis c1 c2 h1 h2 ne x h h'
    · have := bl c1 h1 x h; omega
    · have := bl c2 h2 x h'; omega
    · exact ne (e1.trans e2.symm)
  · rcases hx with h | ⟨_,_,h⟩
    · have := bl c' hc' x h; omega
    · exact h

#print axioms balW_upd
end bv
end InitECandidate.Runtime
