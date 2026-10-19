import InitECandidate.Runtime.HtrPayloadSource
namespace InitECandidate.Runtime

theorem hashRoot_output_geometry (roots index : BitVec 64) (count : Nat)
    (inside : index.toNat < count) (aligned : roots.toNat % 8 = 0)
    (fits : roots.toNat + count * 32 ≤ 33806089496) :
    (roots + index * (32#64)).toNat = roots.toNat + index.toNat * 32 ∧
      (roots + index * (32#64)).toNat % 8 = 0 ∧
      (roots + index * (32#64)).toNat + 32 ≤ 33806089496 := by
  have offset : (index * (32#64)).toNat = index.toNat * 32 := by
    apply BitVec.toNat_mul_of_lt
    change index.toNat * 32 < 2 ^ 64
    omega
  have natural : (roots + index * (32#64)).toNat = roots.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [offset]; omega),offset]
  refine ⟨natural,?_,by rw [natural]; omega⟩
  rw [natural,Nat.add_mod,Nat.mul_mod,aligned]
  simp

#print axioms hashRoot_output_geometry
end InitECandidate.Runtime
