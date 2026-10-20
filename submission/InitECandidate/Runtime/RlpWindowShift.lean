import InitECandidate.Runtime.RlpPutBeWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A window of eight bytes at `dst + 1` sits inside the nine-byte window at `dst`; this is the
address arithmetic that lifts the `rlp_put_be` callee window back to its `rlp_write_header` caller. -/
theorem mwin_shift_one {D w : BitVec 64} {L : Nat} (h : MWin (D + 1#64) L w) (hL : L ≤ 8) :
    MWin D 9 w := by
  obtain ⟨j,hj,he⟩ := h
  have hjlt : j < 8 := by omega
  have hj9 : j + 1 < 9 := by omega
  have hbound : j + 1 < 2 ^ 64 := by omega
  have hstep : (D + 1#64) + BitVec.ofNat 64 j = D + BitVec.ofNat 64 (j + 1) := by
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.toNat_inj.mp
    have hj64 : j < 2 ^ 64 := by omega
    have h1j : 1 + j < 2 ^ 64 := by omega
    rw [BitVec.toNat_add]
    rw [show (1#64 : BitVec 64).toNat = 1 from by decide]
    rw [show (BitVec.ofNat 64 j).toNat = j from by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hj64]
    rw [show (1 + j) % 2 ^ 64 = 1 + j from Nat.mod_eq_of_lt h1j]
    rw [show (BitVec.ofNat 64 (j + 1)).toNat = j + 1 from by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hbound]
    omega
  refine ⟨j + 1,hj9,?_⟩
  rcases he with he | he
  · exact Or.inl (he.trans hstep)
  · exact Or.inr (he.trans (congrArg panByteAlignHOL hstep))

#print axioms mwin_shift_one

end InitECandidate.Runtime
