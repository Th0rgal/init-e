import InitECandidate.Runtime.AllocationSeparation
import InitECandidate.Runtime.SourceByteReadback
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Byte-level invariant for the completed prefix of memzero. -/
def ZeroBytePrefix {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : BitVec 64) (length : Nat) : Prop :=
  ∀ offset : Nat, offset < length →
    hashOccupancyRead state destination (BitVec.ofNat 64 offset) = some 0

theorem byteAlign_in_word (base current : BitVec 64) (aligned : base.toNat % 8 = 0)
    (lower : base.toNat ≤ current.toNat) (upper : current.toNat < base.toNat + 8) :
    panByteAlignHOL current = base := by
  apply BitVec.eq_of_toNat_eq
  rw [panByteAlign_toNat64]
  have baseDivision := Nat.mod_add_div base.toNat 8
  have currentDivision := Nat.mod_add_div current.toNat 8
  have currentRemainder := Nat.mod_lt current.toNat (by decide : 0 < 8)
  omega

/-- Reading any byte of a word just zeroed returns zero, in both endiannesses. -/
theorem sourceWriteWord_zero_byte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination current : BitVec 64) (aligned : panByteAlignHOL current = destination)
    (domain : state.memaddrs destination) :
    @panMemLoadByteHOL 64 _ (sourceWriteWord state destination 0).memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be current = some 0 := by
  simp [panMemLoadByteHOL,sourceWriteWord,aligned,domain,panGetByteHOL]

/-- A full aligned zero word extends an already completed byte prefix by eight,
while leaving the preceding prefix intact. -/
theorem ZeroBytePrefix.extend_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : BitVec 64) (length : Nat)
    (zero : ZeroBytePrefix state destination length)
    (aligned : (destination.toNat + length) % 8 = 0)
    (bounded : destination.toNat + length + 8 ≤ 2 ^ 64)
    (domain : state.memaddrs (destination + BitVec.ofNat 64 length)) :
    ZeroBytePrefix (sourceWriteWord state (destination + BitVec.ofNat 64 length) 0) destination (length + 8) := by
  have addressNat (offset : Nat) (inside : offset < length + 8) :
      (destination + BitVec.ofNat 64 offset).toNat = destination.toNat + offset := by
    have wordBound : offset < 2 ^ 64 := by omega
    have small : destination.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt wordBound]
      omega
    rw [BitVec.toNat_add_of_lt small,BitVec.toNat_ofNat,Nat.mod_eq_of_lt wordBound]
  have blockNat := addressNat length (by omega)
  intro offset inside
  by_cases before : offset < length
  · have different : panByteAlignHOL (destination + BitVec.ofNat 64 offset) ≠
        destination + BitVec.ofNat 64 length := by
      intro equal
      have same := congrArg BitVec.toNat equal
      rw [panByteAlign_toNat64,addressNat offset inside,blockNat] at same
      have quotient := Nat.div_mul_le_self (destination.toNat + offset) 8
      omega
    have preserved : hashOccupancyRead (sourceWriteWord state (destination + BitVec.ofNat 64 length) 0)
        destination (BitVec.ofNat 64 offset) = hashOccupancyRead state destination (BitVec.ofNat 64 offset) := by
      simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,different]
      rfl
    exact preserved.trans (zero offset before)
  · have sameWord : panByteAlignHOL (destination + BitVec.ofNat 64 offset) =
        destination + BitVec.ofNat 64 length := by
      apply byteAlign_in_word
      · simpa only [blockNat] using aligned
      · rw [blockNat,addressNat offset inside]; omega
      · rw [blockNat,addressNat offset inside]; omega
    exact sourceWriteWord_zero_byte state _ _ sameWord domain

/-- The exact final-byte store extends coverage without disturbing any earlier
byte, including earlier bytes in the same aligned memory word. -/
theorem ZeroBytePrefix.extend_byte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination cell : BitVec 64) (length : Nat)
    (zero : ZeroBytePrefix state destination length)
    (bounded : destination.toNat + length + 1 ≤ 2 ^ 64)
    (domain : state.memaddrs (panByteAlignHOL (destination + BitVec.ofNat 64 length)))
    (memory : state.memory (panByteAlignHOL (destination + BitVec.ofNat 64 length)) = .word cell) :
    ZeroBytePrefix (sourceWriteByte state (destination + BitVec.ofNat 64 length) 0 cell) destination (length + 1) := by
  have indexBound : length < 2 ^ 64 := by omega
  intro offset inside
  by_cases before : offset < length
  · have distinctWords : BitVec.ofNat 64 offset ≠ BitVec.ofNat 64 length := by
      intro same
      have equal := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexBound,
        Nat.mod_eq_of_lt (show offset < 2 ^ 64 by omega)] at equal
      omega
    have different : destination + BitVec.ofNat 64 offset ≠ destination + BitVec.ofNat 64 length := by
      simpa using distinctWords
    have preserved := sourceWriteByte_load_other state (destination + BitVec.ofNat 64 length) 0 cell
      (destination + BitVec.ofNat 64 offset) different memory
    exact preserved.trans (zero offset before)
  · have same : offset = length := by omega
    subst offset
    exact sourceWriteByte_load_self state (destination + BitVec.ofNat 64 length) 0 cell domain

/-- A completed source zero-fill establishes the actual occupancy count zero. -/
theorem ZeroBytePrefix.occupancy_zero {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination capacity : BitVec 64) (zero : ZeroBytePrefix state destination capacity.toNat) :
    hashOccupiedCount capacity (hashOccupancyRead state destination) = 0 := by
  apply hashOccupiedCount_zero
  intro index inside
  have loaded := zero index.toNat inside
  simpa using loaded

#print axioms ZeroBytePrefix.extend_byte
#print axioms ZeroBytePrefix.occupancy_zero
#print axioms byteAlign_in_word
#print axioms sourceWriteWord_zero_byte
#print axioms ZeroBytePrefix.extend_word
end InitECandidate.Runtime
