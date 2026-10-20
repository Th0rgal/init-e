import InitECandidate.Runtime.RlpEncodeBytesWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Widening a store window by any constant offset: writes inside the `N` bytes at `D + k` are
writes inside the `k + N` bytes at `D`. -/
theorem mwin_shift_nat {D : BitVec 64} {k N : Nat} {w : BitVec 64}
    (win : MWin (D + BitVec.ofNat 64 k) N w) : MWin D (k + N) w := by
  have inner : ∀ j : Nat, D + BitVec.ofNat 64 k + BitVec.ofNat 64 j = D + BitVec.ofNat 64 (k + j) := by
    intro j
    rw [BitVec.add_assoc]
    congr 1
    rw [BitVec.ofNat_add]
  obtain ⟨j, hj, hw | hw⟩ := win
  · exact ⟨k + j, by omega, Or.inl (hw.trans (inner j))⟩
  · exact ⟨k + j, by omega, Or.inr (by rw [hw]; exact congrArg panByteAlignHOL (inner j))⟩

#print axioms mwin_shift_nat

/-- A store window `n` bytes after the offset `k` sits inside the `64`-byte buffer window at `D`
whenever the whole writer offset fits: no cell outside the buffer window is written. -/
theorem mwin_narrow_shift {D : BitVec 64} {k n : Nat} {w : BitVec 64}
    (out : ¬ MWin D 64 w) (fit : k + n ≤ 64) : ¬ MWin (D + BitVec.ofNat 64 k) n w :=
  fun win => (mwin_mono fit out) (mwin_shift_nat win)

#print axioms mwin_narrow_shift

end InitECandidate.Runtime
