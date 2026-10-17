import InitECandidate.Runtime.MemzeroCoverage
import Flapjack.Pancake.Semantics.ShMemBytesBridge
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Eight zero byte projections determine the entire word in either endian. -/
theorem word_zero_of_panBytes (word : BitVec 64) (be : Bool)
    (bytes : ∀ residue : Nat, residue < 8 → panGetByteHOL (BitVec.ofNat 64 residue) word be = 0) :
    word = 0 := by
  apply panWord_eq_of_getByte_eq (by decide : 64 % 8 = 0)
  intro residue small
  have small64 : residue < 2^64 := by omega
  cases be with
  | false =>
    have zero := bytes residue small
    rw [zero]
    simp [panGetByteHOL]
  | true =>
    have reverseSmall : 7 - residue < 8 := by omega
    have reverse64 : 7 - residue < 2^64 := by omega
    have reversed : panGetByteHOL (BitVec.ofNat 64 (7 - residue)) word true =
        panGetByteHOL (BitVec.ofNat 64 residue) word false := by
      simp only [panGetByteHOL,BitVec.toNat_ofNat]
      have index : 64 / 8 - 1 - ((7 - residue) % 2^64 % (64 / 8)) = residue % 2^64 % (64 / 8) := by omega
      rw [index]
      rfl
    have zero := bytes (7 - residue) reverseSmall
    rw [reversed] at zero
    rw [zero]
    simp [panGetByteHOL]

/-- Zero-byte coverage yields every fully covered aligned zero memory word. -/
theorem ZeroBytePrefix.word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : BitVec 64) (length offset : Nat)
    (zero : ZeroBytePrefix state destination length)
    (inside : offset + 8 ≤ length) (bounded : destination.toNat + length < 2^64)
    (aligned : (destination.toNat + offset) % 8 = 0) :
    state.memory (destination + BitVec.ofNat 64 offset) = .word 0 := by
  let base := destination + BitVec.ofNat 64 offset
  have natural (n : Nat) (small : n < length) :
      (destination + BitVec.ofNat 64 n).toNat = destination.toNat + n := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  have baseNat : base.toNat = destination.toNat + offset := natural offset (by omega)
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64, state.memory base = .word cell := by
    cases state.memory base with | word cell => exact ⟨cell,rfl⟩
  have cellZero : cell = 0 := by
    apply word_zero_of_panBytes cell state.be
    intro residue small
    have readZero := zero (offset + residue) (by omega)
    have addressNat := natural (offset + residue) (by omega)
    have sameWord : panByteAlignHOL (destination + BitVec.ofNat 64 (offset + residue)) = base :=
      byteAlign_in_word base _ (by rw [baseNat]; exact aligned)
        (by rw [baseNat,addressNat]; omega) (by rw [baseNat,addressNat]; omega)
    have byteZero : panGetByteHOL (destination + BitVec.ofNat 64 (offset + residue)) cell state.be = 0 := by
      unfold hashOccupancyRead at readZero
      simp only [panMemLoadByteHOL,sameWord,cellRead] at readZero
      split at readZero
      · exact Option.some.inj readZero
      · cases readZero
    have residueEq : (destination + BitVec.ofNat 64 (offset + residue)).toNat % 8 = residue := by
      rw [addressNat]
      omega
    have literal : (BitVec.ofNat 64 residue).toNat % 8 = residue := by
      rw [BitVec.toNat_ofNat]
      omega
    simpa only [panGetByteHOL,residueEq,literal] using byteZero
  rw [cellRead,cellZero]

#print axioms ZeroBytePrefix.word
#print axioms word_zero_of_panBytes
end InitECandidate.Runtime
