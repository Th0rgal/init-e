import InitECandidate.Runtime.HashDeleteLoopStepPhysicalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete ranked deletion scan preserves the other live table. -/
theorem evaluate_hashDelete_loop_physical_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      (HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
       HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock := by
  let combined := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits current ∧
    HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer current
  have bounds := valid.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,postValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_supported combined
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.1.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => ⟨currentValid.1.dec_clock keyLength table keys stride capacity used values order orderPos items empty bits current,
      currentValid.2.after_read current (decClockHOLFinite current) otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.1.step_supported_with_physical_table keyLength table keys stride capacity used values order orderPos items empty bits current
      otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits currentValid.2 separated supported ticks)
    state ⟨valid,ready⟩ (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,postValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_loop_physical_supported
end InitECandidate.Runtime
