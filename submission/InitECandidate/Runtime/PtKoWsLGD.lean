import InitECandidate.Runtime.PtRegTRGD
import InitECandidate.Runtime.HtabInsertRawFrame
import InitECandidate.Runtime.StoreLoopWindow
/-!
Repair of the unsatisfiable `hkoWs` premise (`hkoWs_form_false`). The workspace words (frame arena `[FM, SP0)`, keccak
state `K` (200 bytes), padding `Pd` (136 bytes), nibble scratch `NB` (64 bytes)) all lie below a floor `L0`
(`wsSafe_of_low`). A valid layout of a table at `Tt` (`lo.ok Tt Hx`) places its header at `Tt` and every array after
it, so a table with `L0 ≤ Tt` has all its words above the floor, at its *current* layout, whatever moves and growth
happened (`koWsL_of_low`). The satisfiable replacement premise `KoWsL` (memory-free, layout-validity constrained) gives
the fixed-memory form used inside the callee proofs from the registry's own layout (`koWs_fixed`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every word of any validly laid-out table at `Tt` (at any heap pointer) satisfies `P`. -/
def TabAvoid (P : BitVec 64 → Prop) (Tt : BitVec 64) : Prop :=
  ∀ (lo : TLay) (Hx : BitVec 64), lo.ok Tt Hx → ∀ x, InTabF Tt lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → P x

theorem tabAvoid_of_low {P : BitVec 64 → Prop} {L0 Tt : BitVec 64} (hP : ∀ x : BitVec 64, L0.toNat ≤ x.toNat → P x)
    (hT : L0.toNat ≤ Tt.toNat) : TabAvoid P Tt := by
  intro lo Hx ok x hx
  apply hP
  have k := ok.keysR.1; have v := ok.valsR.1; have u := ok.usedR.1; have o := ok.orderR.1; have op := ok.oposR.1
  rcases hx with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> omega

#print axioms tabAvoid_of_low

/-- The repaired premise: every word of any validly laid-out table at `Tt` is off the workspaces. -/
def KoWsL (SP0 FM K Pd NB Tt : BitVec 64) : Prop :=
  ∀ (lo : TLay) (Hx : BitVec 64), lo.ok Tt Hx →
    ∀ x, InTabF Tt lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x

/-- Workspaces below the floor `L0`: every word at or above it is off the workspaces. -/
theorem wsSafe_of_low {SP0 FM K Pd NB L0 : BitVec 64} (hSP : SP0.toNat ≤ L0.toNat)
    (hK : K.toNat + 200 ≤ L0.toNat) (hPd : Pd.toNat + 136 ≤ L0.toNat) (hNB : NB.toNat + 64 ≤ L0.toNat)
    (x : BitVec 64) (hx : L0.toNat ≤ x.toNat) : WsSafe SP0 FM K Pd NB x := by
  have win : ∀ (S : BitVec 64) (N : Nat), S.toNat + N ≤ L0.toNat → ¬ MWin S N x := by
    intro S N hS ⟨j,hj,h⟩
    have e : (S + BitVec.ofNat 64 j).toNat = S.toNat + j := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    rcases h with rfl | rfl
    · rw [e] at hx; omega
    · rw [byteAlign_toNat,e] at hx
      have := Nat.div_mul_le_self (S.toNat + j) 8
      omega
  refine ⟨Or.inr (by omega),win K 200 hK,win Pd 136 hPd,fun j hj h => ?_⟩
  have e : (NB + BitVec.ofNat 64 j).toNat = NB.toNat + j := by
    rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  rw [h,byteAlign_toNat,e] at hx
  have := Nat.div_mul_le_self (NB.toNat + j) 8
  omega

/-- A table at or above the floor: all its words, at any valid current layout, are off the workspaces. -/
theorem koWsL_of_low {SP0 FM K Pd NB L0 Tt : BitVec 64} (hws : ∀ x : BitVec 64, L0.toNat ≤ x.toNat →
    WsSafe SP0 FM K Pd NB x) (hT : L0.toNat ≤ Tt.toNat) : KoWsL SP0 FM K Pd NB Tt := by
  intro lo Hx ok x hx
  apply hws
  have k := ok.keysR.1; have v := ok.valsR.1; have u := ok.usedR.1; have o := ok.orderR.1; have op := ok.oposR.1
  rcases hx with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> omega

/-- The fixed-memory form at a registry's memory, from the repaired premise. -/
theorem koWs_fixed {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {D : BitVec 64 → Prop} {B : Bool} {ko : Fin n} {SP0 FM K Pd NB : BitVec 64}
    (hL : KoWsL SP0 FM K Pd NB (T ko)) (reg : RegT n c T Out H M D B ko) :
    ∀ lo : TLay, lo.hdr M (T ko) → ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x →
      WsSafe SP0 FM K Pd NB x := by
  obtain ⟨l,pure,mem,_,_⟩ := reg
  intro lo hd x hx
  obtain ⟨_,e1,e2,_,e4,e5,e6,e7,e8⟩ := hdr_unique hd (mem ko).2
  refine hL (l ko) H (pure.1 ko).1 x ?_
  rw [e1,e2,e4,e5,e6,e7,e8]; exact hx

#print axioms wsSafe_of_low
#print axioms koWsL_of_low
#print axioms koWs_fixed
end InitECandidate.Runtime
