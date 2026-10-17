import InitECandidate.Runtime.HashDeleteLoopStepSupported
import InitECandidate.Runtime.HashDeleteOccupiedIterationPhysicalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The ranked scan step carries both the target invariant and another table. -/
theorem HashDeleteLoopInvariantWidth.step_supported_with_physical_table {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : 54 ≤ state.clock) :
    ∃ post, (HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∧
      state.clock ≤ post.clock + 54 ∧ post.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∨
       (evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧
        hashDeleteStateRank capacity empty post < hashDeleteStateRank capacity empty state)) := by
  classical
  have width : keyLength.toNat ≤ 52 := by
    rcases supported with rfl | rfl | rfl <;> decide
  obtain ⟨post,postValid,cost,remaining,body⟩ := valid.step_supported keyLength table keys stride capacity used values order orderPos items empty bits state supported budget
  obtain ⟨hole,index,holeInside,indexInside,holeLocal,indexLocal,holeOccupied⟩ := valid.indices
  let next := hashProbeNext index capacity
  have nextInside : next.toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits valid.arrays.power indexInside]
    exact Nat.mod_lt _ (by rw [valid.arrays.power]; exact Nat.two_pow_pos bits)
  have preserved : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post := by
    by_cases emptyNext : hashOccupancyRead state used next = some 0
    · obtain ⟨checked,run,_,_,_,_,_,memory,globals,code,domain,endian,_,_⟩ :=
        evaluate_hashDelete_empty_allocated_iteration_width state keyLength table keys stride capacity used values order orderPos items index bits
          valid.arrays valid.valuesWord valid.reverse valid.ordered indexLocal valid.capacityLocal valid.usedLocal emptyNext
      have same : post = checked := by
        rcases body with stopped | running
        · exact congrArg Prod.snd (stopped.symm.trans run)
        · have bad := congrArg Prod.fst (running.1.symm.trans run)
          contradiction
      rw [same]
      exact ready.after_read state checked otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code domain endian
    · obtain ⟨checked,run,checkedReady,_,_,_,_,_,_⟩ :=
        evaluate_hashDelete_occupied_iteration_physical_supported state keyLength keys stride hole index values order orderPos used capacity items
          valid.keysLocal valid.strideLocal holeLocal indexLocal valid.sizeLocal valid.usedLocal valid.capacityLocal
          table bits supported valid.arrays nextInside emptyNext valid.keyValueOrder (by omega) valid.valuesLocal valid.orderLocal valid.reverseLocal
          valid.reverse valid.ordered holeInside valid.valuesWord
          otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits ready separated
      have same : post = checked := by
        rcases body with stopped | running
        · have bad := congrArg Prod.fst (stopped.symm.trans run)
          contradiction
        · exact congrArg Prod.snd (running.1.symm.trans run)
      rw [same]
      exact checkedReady
  exact ⟨post,⟨postValid,preserved⟩,cost,remaining,body⟩

#print axioms HashDeleteLoopInvariantWidth.step_supported_with_physical_table
end InitECandidate.Runtime
