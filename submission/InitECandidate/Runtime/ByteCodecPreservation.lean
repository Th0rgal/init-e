import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Misc.GetByteSetByte
namespace InitECandidate.Runtime
open Flapjack
open Flapjack.Compiler.Backend.LabToTarget

/-- Bridge the source UInt8 reader to the reviewed HOL byte extraction. -/
theorem panGetByte_eq_holByte (address cell : BitVec 64) (be : Bool) :
    panGetByteHOL address cell be = UInt8.ofBitVec (HolByte.getByte address cell be) := by
  apply UInt8.toNat.inj
  cases be <;>
    simp [panGetByteHOL,HolByte.getByte,HolByte.byteIndex,BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow,show (256 : Nat) = 2^8 by decide,Nat.pow_mul]

/-- Read back the byte just written, for either endianness. -/
theorem panGetByte_panSetByte_self (address cell : BitVec 64) (byte : BitVec 8) (be : Bool) :
    panGetByteHOL address (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) cell be) be =
      UInt8.ofBitVec byte := by
  rw [panGetByte_eq_holByte,panSetByteHOL_eq_setByteHOL8,setByteHOL8_eq,
    goodDimindex_getByte_setByte address byte cell be (by exact Or.inr rfl)]

/-- Updating one byte preserves every other byte of its aligned word. -/
theorem panGetByte_panSetByte_other (address current cell : BitVec 64) (byte : BitVec 8) (be : Bool)
    (different : current ≠ address) (aligned : panByteAlignHOL current = panByteAlignHOL address) :
    panGetByteHOL current (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) cell be) be =
      panGetByteHOL current cell be := by
  have holAligned : holByteAlign current = holByteAlign address := by
    rw [← riscvByteAlignHOL_eq (by exact Or.inr rfl : goodDimindex 64),
      ← riscvByteAlignHOL_eq (by exact Or.inr rfl : goodDimindex 64),
      riscvByteAlignHOL_eq_panByteAlignHOL,riscvByteAlignHOL_eq_panByteAlignHOL]
    exact aligned
  rw [panGetByte_eq_holByte,panGetByte_eq_holByte,panSetByteHOL_eq_setByteHOL8,setByteHOL8_eq,
    getByte_setByte_diff current address byte cell be ⟨Or.inr rfl,different,holAligned⟩]

#print axioms panGetByte_eq_holByte
#print axioms panGetByte_panSetByte_self
#print axioms panGetByte_panSetByte_other
end InitECandidate.Runtime
