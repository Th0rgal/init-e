import InitECandidate.Runtime.HashFindTail32
import InitECandidate.Runtime.HashFindTableCapacity20
import InitECandidate.Runtime.HashFindTableCapacity52
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindTail20 {F : Type} (table keys stride capacity used values order orderPos count key empty : BitVec 64)
    (bits : Nat) (emptyInside : empty.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant 20 keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindTail =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ := evaluate_hashFind_table_loop20_capacity
    table keys stride capacity used values order orderPos count key empty bits emptyInside keyAligned
    state index valid arrays budget
  unfold hashFindTail
  rw [evaluateHOLFiniteState_seq_line780,run]
  rcases outcome with normal | matched
  · obtain ⟨finalIndex,finalValid,finalArrays⟩ := finalInvariant normal
    rw [normal]
    have returned : evaluateHOLFiniteState post (.return (.var .local (ofString "cap"))) =
        (some (.returned (.val (.word capacity))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,finalValid.capLocal,shapeOfHOLExact]
    exact ⟨capacity,emptyLocalsHOLFinite post,returned,Nat.le_refl _,cost,remaining,memory,globals,code,addresses,endian⟩
  · obtain ⟨found,inside,matched⟩ := matched
    rw [matched]
    exact ⟨found,post,rfl,Nat.le_of_lt inside,cost,remaining,memory,globals,code,addresses,endian⟩


theorem evaluate_hashFindTail52 {F : Type} (table keys stride capacity used values order orderPos count key empty : BitVec 64)
    (bits : Nat) (emptyInside : empty.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant 52 keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindTail =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ := evaluate_hashFind_table_loop52_capacity
    table keys stride capacity used values order orderPos count key empty bits emptyInside keyAligned
    state index valid arrays budget
  unfold hashFindTail
  rw [evaluateHOLFiniteState_seq_line780,run]
  rcases outcome with normal | matched
  · obtain ⟨finalIndex,finalValid,finalArrays⟩ := finalInvariant normal
    rw [normal]
    have returned : evaluateHOLFiniteState post (.return (.var .local (ofString "cap"))) =
        (some (.returned (.val (.word capacity))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,finalValid.capLocal,shapeOfHOLExact]
    exact ⟨capacity,emptyLocalsHOLFinite post,returned,Nat.le_refl _,cost,remaining,memory,globals,code,addresses,endian⟩
  · obtain ⟨found,inside,matched⟩ := matched
    rw [matched]
    exact ⟨found,post,rfl,Nat.le_of_lt inside,cost,remaining,memory,globals,code,addresses,endian⟩


#print axioms evaluate_hashFindTail20
#print axioms evaluate_hashFindTail52
end InitECandidate.Runtime
