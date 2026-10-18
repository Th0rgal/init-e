import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime

def packBytesCount (n : BitVec 64) : BitVec 64 := (n + (31#64)) >>> 5

theorem packBytes_lengths (n : BitVec 64) (small : n.toNat ≤ 134217712) :
    (packBytesCount n).toNat = (n.toNat + 31) / 32 ∧
      (packBytesCount n).toNat ≤ 4194304 ∧
      (packBytesCount n * (32#64)).toNat = (packBytesCount n).toNat * 32 ∧
      n.toNat ≤ (packBytesCount n).toNat * 32 ∧
      ((packBytesCount n * (32#64)) - n).toNat < 32 := by
  have addNatural : (n + (31#64)).toNat = n.toNat + 31 := BitVec.toNat_add_of_lt (by change n.toNat + 31 < 2 ^ 64; omega)
  have countNatural : (packBytesCount n).toNat = (n.toNat + 31) / 32 := by
    simp [packBytesCount,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,addNatural]
  have division := Nat.mod_add_div (n.toNat + 31) 32
  have remainder := Nat.mod_lt (n.toNat + 31) (by decide : 0 < 32)
  have countBound : (packBytesCount n).toNat ≤ 4194304 := by rw [countNatural]; omega
  have mulNatural : (packBytesCount n * (32#64)).toNat = (packBytesCount n).toNat * 32 := by
    rw [BitVec.toNat_mul]
    change ((packBytesCount n).toNat * 32) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have covers : n.toNat ≤ (packBytesCount n).toNat * 32 := by rw [countNatural]; omega
  refine ⟨countNatural,countBound,mulNatural,covers,?_⟩
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [mulNatural]; exact covers)),mulNatural,countNatural]
  omega

#print axioms packBytes_lengths
end InitECandidate.Runtime
