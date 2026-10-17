import InitECandidate.Runtime.HashFindTail32
import InitECandidate.Runtime.HashFindInvariantOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_hashFindTail32_occupied {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindTail =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ := evaluate_hashFindLoop32_capacity_occupied
    keys stride key capacity used empty bits power emptyInside keysAligned strideAligned keyAligned strideFits bounded
    state index valid budget
  unfold hashFindTail
  rw [evaluateHOLFiniteState_seq_line780,run]
  rcases outcome with normal | matched
  · obtain ⟨finalIndex,finalValid⟩ := finalInvariant normal
    rw [normal]
    have returned : evaluateHOLFiniteState post (.return (.var .local (ofString "cap"))) =
        (some (.returned (.val (.word capacity))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,finalValid.capLocal,shapeOfHOLExact]
    exact ⟨capacity,emptyLocalsHOLFinite post,returned,Nat.le_refl _,(by intro impossible; exact False.elim (impossible rfl)),cost,remaining,memory,globals,code,addresses,endian⟩
  · obtain ⟨found,inside,occupied,matched⟩ := matched
    rw [matched]
    exact ⟨found,post,rfl,Nat.le_of_lt inside,(fun _ => occupied),cost,remaining,memory,globals,code,addresses,endian⟩

#print axioms evaluate_hashFindTail32_occupied
end InitECandidate.Runtime
