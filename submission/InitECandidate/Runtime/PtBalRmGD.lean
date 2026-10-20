import InitECandidate.Runtime.PtBalLstGD
/-!
The actual `bal_list_remove_idx(l, esz, idx)` on a valid list header at `Lh` (`buf P, n N, cap Cp`, 8-aligned buffer
and element size): the scan reads the entries only; a found entry `i < N` is overwritten by the last one (`memcpy`
inside the buffer) and the count becomes `N - 1`. Only the header count word and buffer words change; the buffer and
capacity stay.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Postcondition of `bal_list_remove_idx`. -/
def LRPost (Lh E P N Cp : BitVec 64) (M0 : Mem) (Gk : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) : Prop :=
  G' = Gk ∧ ∃ N' : BitVec 64, LHd Lh P N' Cp M' ∧ N'.toNat ≤ N.toNat ∧
    ∀ x, ¬ HdW Lh x → ¬ (P.toNat ≤ x.toNat ∧ x.toNat < P.toNat + E.toNat * Cp.toNat) → M' x = M0 x

section lr
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- A window inside the buffer lies in the buffer. -/
theorem mwin_in_buf {P E Cp Iv x : BitVec 64} (hP8 : P.toNat % 8 = 0) (hE8 : E.toNat % 8 = 0)
    (hI : Iv.toNat < Cp.toNat) (fit : P.toNat + E.toNat * Cp.toNat < 2 ^ 64)
    (eD : (P + Iv * E).toNat = P.toNat + Iv.toNat * E.toNat) (hx : MWin (P + Iv * E) E.toNat x) :
    P.toNat ≤ x.toNat ∧ x.toNat < P.toNat + E.toNat * Cp.toNat := by
  have sa := slot_arith (E := E.toNat) hI
  have al : (P + Iv * E).toNat % 8 = 0 := by
    rw [eD]; have := Nat.mul_mod Iv.toNat E.toNat 8; rw [hE8] at this; simp at this; omega
  obtain ⟨lo,hi⟩ := mwin_ge hx al (by rw [eD]; omega)
  rw [eD] at lo hi
  constructor <;> omega

end lr
end InitECandidate.Runtime
