import InitECandidate.Runtime.HashDeleteLoopStepOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete ranked deletion scan preserves the other live table. -/
theorem evaluate_hashDelete_loop_other32 {F : Type}
    (table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits state)
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (budget : capacity.toNat * 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      (HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits post ∧
       HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∧
      state.clock ≤ post.clock + capacity.toNat * 35 ∧ post.clock ≤ state.clock := by
  let combined := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLoopInvariant32 table keys stride capacity used values order orderPos items empty bits current ∧
    HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer current
  have bounds := valid.rank_bounds table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,postValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked combined
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.1.rank_bounds table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => ⟨currentValid.1.dec_clock table keys stride capacity used values order orderPos items empty bits current,
      currentValid.2.after_read current (decClockHOLFinite current) otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.1.step_with_other table keys stride capacity used values order orderPos items empty bits current
      otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits currentValid.2 separated ticks)
    state ⟨valid,ready⟩ (Nat.le_trans (Nat.mul_le_mul_right 35 bounds.2) budget)
  exact ⟨post,run,postValid,by have := Nat.mul_le_mul_right 35 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_loop_other32
end InitECandidate.Runtime
