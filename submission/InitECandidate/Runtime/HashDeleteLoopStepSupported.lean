import InitECandidate.Runtime.HashDeleteLoopInvariantWidth
import InitECandidate.Runtime.HashDeleteLoopRankedSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashDeleteLoopInvariantWidth.step_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : 54 ≤ state.clock) :
    ∃ post, HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
      state.clock ≤ post.clock + 54 ∧ post.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∨
       (evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧
        hashDeleteStateRank capacity empty post < hashDeleteStateRank capacity empty state)) := by
  classical
  have width : keyLength.toNat ≤ 52 := by
    rcases supported with rfl | rfl | rfl <;> decide
  obtain ⟨hole,index,holeInside,indexInside,holeLocal,indexLocal,holeOccupied⟩ := valid.indices
  let next := hashProbeNext index capacity
  have nextInside : next.toNat < capacity.toNat := by
    rw [hashProbeNext_toNat index capacity bits valid.arrays.power indexInside]
    exact Nat.mod_lt _ (by rw [valid.arrays.power]; exact Nat.two_pow_pos bits)
  by_cases emptyNext : hashOccupancyRead state used next = some 0
  · obtain ⟨post,run,ticks,arrays,words,reverse,ordered,memory,globals,code,domain,endian,scanPost,other⟩ :=
      evaluate_hashDelete_empty_allocated_iteration_width state keyLength table keys stride capacity used values order orderPos items index bits
        valid.arrays valid.valuesWord valid.reverse valid.ordered indexLocal valid.capacityLocal valid.usedLocal emptyNext
    have postValid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post := {
      valid with
      arrays := arrays
      valuesWord := words
      reverse := reverse
      ordered := ordered
      emptyRead := by unfold hashOccupancyRead; rw [memory,domain,endian]; exact valid.emptyRead
      keysLocal := ((other (ofString "keys") (by decide))).trans valid.keysLocal
      strideLocal := ((other (ofString "stride") (by decide))).trans valid.strideLocal
      sizeLocal := ((other (ofString "klen") (by decide))).trans valid.sizeLocal
      capacityLocal := ((other (ofString "cap") (by decide))).trans valid.capacityLocal
      usedLocal := ((other (ofString "used") (by decide))).trans valid.usedLocal
      valuesLocal := ((other (ofString "vals") (by decide))).trans valid.valuesLocal
      orderLocal := ((other (ofString "order") (by decide))).trans valid.orderLocal
      reverseLocal := ((other (ofString "order_pos") (by decide))).trans valid.reverseLocal
      indices := ⟨hole,next,holeInside,nextInside,((other _ (by decide))).trans holeLocal,scanPost,by unfold hashOccupancyRead; rw [memory,domain,endian]; exact holeOccupied⟩
    }
    exact ⟨post,postValid,by omega,by omega,Or.inl run⟩
  · obtain ⟨post,run,cost,remaining,globals,code,domain,endian,reverse,ordered,occupancy,holePost,words,scanPost,arrays,other⟩ :=
      evaluate_hashDelete_occupied_allocated_iteration_supported state keyLength keys stride hole index values order orderPos used capacity items
        valid.keysLocal valid.strideLocal holeLocal indexLocal valid.sizeLocal valid.usedLocal valid.capacityLocal
        table bits supported valid.arrays nextInside emptyNext valid.keyValueOrder (by omega) valid.valuesLocal valid.orderLocal valid.reverseLocal
        valid.reverse valid.ordered holeInside valid.valuesWord
    obtain ⟨newHole,newInside,newLocal,newOccupied⟩ : ∃ newHole : BitVec 64, newHole.toNat < capacity.toNat ∧
        post.locals.lookup (ofString "i") = some (.val (.word newHole)) ∧ hashOccupancyRead post used newHole ≠ some 0 := by
      rcases holePost with oldHole | moved
      · exact ⟨hole,holeInside,oldHole,by rw [occupancy hole holeInside]; exact holeOccupied⟩
      · exact ⟨next,nextInside,moved,by rw [occupancy next nextInside]; exact emptyNext⟩
    have postValid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post := {
      valid with
      arrays := arrays
      valuesWord := words
      reverse := reverse
      ordered := ordered
      emptyRead := (occupancy empty valid.emptyInside).trans valid.emptyRead
      keysLocal := ((other (ofString "keys") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.keysLocal
      strideLocal := ((other (ofString "stride") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.strideLocal
      sizeLocal := ((other (ofString "klen") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.sizeLocal
      capacityLocal := ((other (ofString "cap") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.capacityLocal
      usedLocal := ((other (ofString "used") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.usedLocal
      valuesLocal := ((other (ofString "vals") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.valuesLocal
      orderLocal := ((other (ofString "order") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.orderLocal
      reverseLocal := ((other (ofString "order_pos") (by decide) (by decide) (by decide) (by decide) (by decide))).trans valid.reverseLocal
      indices := ⟨newHole,next,newInside,nextInside,newLocal,scanPost,newOccupied⟩
    }
    have different : next ≠ empty := by intro same; apply emptyNext; rw [same]; exact valid.emptyRead
    have decrease := hashDeleteRank_decreases capacity index empty bits valid.arrays.power indexInside valid.emptyInside different
    have ranked : hashDeleteStateRank capacity empty post < hashDeleteStateRank capacity empty state := by
      rw [hashDeleteStateRank_of_local capacity empty next post scanPost,
        hashDeleteStateRank_of_local capacity empty index state indexLocal]
      exact decrease
    exact ⟨post,postValid,by omega,remaining,Or.inr ⟨run,ranked⟩⟩

/-- The actual deletion scan terminates within 55 clocks per table slot. -/
theorem evaluate_hashDelete_loop_capacity_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock := by
  have bounds := valid.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,postValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_supported
    (HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits)
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => currentValid.dec_clock keyLength table keys stride capacity used values order orderPos items empty bits current)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.step_supported keyLength table keys stride capacity used values order orderPos items empty bits current supported ticks)
    state valid (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,postValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_loop_capacity_supported

#print axioms HashDeleteLoopInvariantWidth.step_supported
end InitECandidate.Runtime
