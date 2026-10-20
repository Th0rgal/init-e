import InitECandidate.Runtime.ComputeJumpdestsSource
import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack

def computeJumpdestsBitmapSize (length : BitVec 64) : BitVec 64 := ((length+63)>>> (6 : Nat))*8+8

theorem compute_jumpdests_bitmap_size_natural (length : BitVec 64) (small : length.toNat≤134217712) :
 (computeJumpdestsBitmapSize length).toNat=(length.toNat+63)/64*8+8 := by
 have sumSmall : length.toNat+(63#64).toNat<2^64 := by change length.toNat+63<2^64;omega
 have sum := BitVec.toNat_add_of_lt sumSmall
 have shift : ((length+63#64)>>> (6 : Nat)).toNat=(length.toNat+63)/64 := by
  rw [BitVec.toNat_ushiftRight,sum,Nat.shiftRight_eq_div_pow]
  rfl
 have mulSmall : (((length+63#64)>>> (6 : Nat)).toNat*8)<2^64 := by
  rw [shift]
  have divLe:=Nat.div_le_self (length.toNat+63) 64
  omega
 have mul : ((((length+63#64)>>> (6 : Nat))*8#64).toNat)=(length.toNat+63)/64*8 := by
  rw [BitVec.toNat_mul]
  change ((length+63#64)>>> (6 : Nat)).toNat*8%2^64=_
  rw [Nat.mod_eq_of_lt mulSmall,shift]
 have addSmall : ((((length+63#64)>>> (6 : Nat))*8#64).toNat)+(8#64).toNat<2^64 := by
  rw [mul]
  change (length.toNat+63)/64*8+8<2^64
  have divLe:=Nat.div_le_self (length.toNat+63) 64
  omega
 change (((length+63#64)>>> (6 : Nat))*8#64+8#64).toNat=_
 rw [BitVec.toNat_add_of_lt addSmall,mul]
 rfl

/-- The guarded program counter selects a full word inside the actual
rounded bitmap allocation, without any accessible-read or allocation premise. -/
theorem compute_jumpdests_bitmap_cell_before_frontier (bitmap length pc : BitVec 64) (frontier : Nat)
 (small : length.toNat≤134217712) (active : pc.toNat<length.toNat)
 (extent : bitmap.toNat+(computeJumpdestsBitmapSize length).toNat≤frontier)
 (cap : frontier≤33806089496) : (bitmap+(pc>>> (6 : Nat))*8).toNat+8≤frontier := by
 have lengthSize:=compute_jumpdests_bitmap_size_natural length small
 have pcShift : (pc>>> (6 : Nat)).toNat=pc.toNat/64 := by rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
 have order : pc.toNat/64≤(length.toNat+63)/64 := Nat.div_le_div_right (by omega)
 have mulSmall : (pc>>> (6 : Nat)).toNat*(8#64).toNat<2^64 := by
  rw [pcShift]
  change pc.toNat/64*8<2^64
  have divLe:=Nat.div_le_self pc.toNat 64
  omega
 have mul : ((pc>>> (6 : Nat))*8#64).toNat=pc.toNat/64*8 := by
  rw [BitVec.toNat_mul,Nat.mod_eq_of_lt mulSmall,pcShift];rfl
 have sumSmall : bitmap.toNat+((pc>>> (6 : Nat))*8#64).toNat<2^64 := by rw [mul];omega
 change (bitmap+(pc>>> (6 : Nat))*8#64).toNat+8≤frontier
 rw [BitVec.toNat_add_of_lt sumSmall,mul]
 omega
#print axioms compute_jumpdests_bitmap_size_natural
#print axioms compute_jumpdests_bitmap_cell_before_frontier
end InitECandidate.Runtime
