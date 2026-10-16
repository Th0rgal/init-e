import InitECandidate.Runtime.HashFindIteration32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual comparison arguments are the indexed key slot, query key and key
width loaded into the original lookup locals. -/
theorem eval_hashFind_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride key keyLength : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength))) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word (keys + index * stride)),.val (.word key),.val (.word keyLength)] := by
  simp [evalListHOLFinite,hashFindComparisonAddress,evalHOLExact,evalListHOLExact,
    keysLocal,indexLocal,strideLocal,keyLocal,lengthLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

/-- A key slot in a heap-bounded array has its ordinary natural address and
retains the array's eight-byte alignment. -/
theorem hashFind_slot_address (keys index stride capacity : BitVec 64)
    (inside : index.toNat < capacity.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0) :
    (keys + index * stride).toNat = keys.toNat + index.toNat * stride.toNat ∧
      (keys + index * stride).toNat % 8 = 0 := by
  have productBound : index.toNat * stride.toNat ≤ capacity.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat (Nat.le_of_lt inside)
  have productSmall : index.toNat * stride.toNat < 2 ^ 64 := by omega
  have product := BitVec.toNat_mul_of_lt productSmall
  have sumSmall : keys.toNat + (index * stride).toNat < 2 ^ 64 := by rw [product]; omega
  have address : (keys + index * stride).toNat = keys.toNat + index.toNat * stride.toNat := by
    rw [BitVec.toNat_add_of_lt sumSmall,product]
  refine ⟨address,?_⟩
  rw [address,Nat.add_mod,Nat.mul_mod,keysAligned,strideAligned]
  simp

/-- Every offset within a key stays inside its allocated array slot, with no
word overflow in the load address. -/
theorem hashFind_slot_offset (keys index stride capacity keyLength : BitVec 64)
    (offset : Nat) (inside : index.toNat < capacity.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (fits : keyLength.toNat ≤ stride.toNat) (offsetInside : offset < keyLength.toNat) :
    (keys + index * stride + BitVec.ofNat 64 offset).toNat =
      keys.toNat + index.toNat * stride.toNat + offset ∧
      keys.toNat ≤ (keys + index * stride + BitVec.ofNat 64 offset).toNat ∧
      (keys + index * stride + BitVec.ofNat 64 offset).toNat <
        keys.toNat + capacity.toNat * stride.toNat := by
  have address := (hashFind_slot_address keys index stride capacity inside bounded keysAligned strideAligned).1
  have nextIndex : index.toNat + 1 ≤ capacity.toNat := by omega
  have nextProduct := Nat.mul_le_mul_right stride.toNat nextIndex
  rw [Nat.add_mul,Nat.one_mul] at nextProduct
  have interval : keys.toNat + index.toNat * stride.toNat + offset <
      keys.toNat + capacity.toNat * stride.toNat := by omega
  have offsetSmall : offset < 2 ^ 64 := by have := keyLength.isLt; omega
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt offsetSmall
  have sumSmall : (keys + index * stride).toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
    rw [address,offsetNat]; omega
  rw [BitVec.toNat_add_of_lt sumSmall,address,offsetNat]
  exact ⟨rfl,by omega,interval⟩

#print axioms hashFind_slot_offset
#print axioms eval_hashFind_arguments
#print axioms hashFind_slot_address
end InitECandidate.Runtime
