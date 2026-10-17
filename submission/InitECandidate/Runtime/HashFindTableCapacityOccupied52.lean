import InitECandidate.Runtime.HashFindTableLoopOccupied52
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Twice the capacity bounds the actual 52-byte lookup scan. -/
theorem evaluate_hashFind_table_loop52_capacity_occupied {F : Type}
    (table keys stride capacity used values order orderPos count key empty : BitVec 64) (bits : Nat)
    (emptyInside : empty.toNat < capacity.toNat) (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant 52 keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ hashOccupancyRead post used found ≠ some 0 ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant 52 keys stride key capacity used empty post finalIndex ∧
        HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits post) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat valid.inside emptyInside
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,domain,endian⟩ :=
    evaluate_hashFind_table_loop52_occupied table keys stride capacity used values order orderPos count key empty bits emptyInside keyAligned state index valid arrays (by omega)
  exact ⟨result,post,run,by omega,remaining,outcome,finalInvariant,memory,globals,code,domain,endian⟩

#print axioms evaluate_hashFind_table_loop52_capacity_occupied
end InitECandidate.Runtime
