import InitECandidate.Runtime.HashFindInvariant
import InitECandidate.Runtime.HashFindTableOccupied52
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual 52-byte lookup scan terminates within twice the cyclic rank. -/
theorem evaluate_hashFind_table_loop52 {F : Type}
    (table keys stride capacity used values order orderPos count key empty : BitVec 64) (bits : Nat)
    (emptyInside : empty.toNat < capacity.toNat) (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant 52 keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant 52 keys stride key capacity used empty post finalIndex ∧
        HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits post) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let combined := fun (current : PanSemStateFiniteExact 64 F) (probe : BitVec 64) => HashFindInvariant 52 keys stride key capacity used empty current probe ∧
    HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits current
  apply evaluate_hashFindLoop_rank capacity empty used bits arrays.power emptyInside combined
    (fun _ _ h => ⟨h.1.indexLocal,h.1.usedLocal⟩)
    (fun _ _ h => h.1.readable _ h.1.inside) (fun _ _ h => h.1.emptyLoad) ?_
    _ state index ⟨valid,arrays⟩ valid.inside rfl budget
  intro current probe byte h inside enough loaded occupied
  obtain ⟨result,post,run,outcome,ticks,memory,globals,code,domain,endian,_,locals⟩ :=
    evaluate_hashFind_table_occupied52 current table keys stride capacity used values order orderPos count key probe bits h.2 enough inside
      keyAligned h.1.keyWords h.1.keyBytes h.1.keysLocal h.1.strideLocal h.1.keyLocal h.1.lengthLocal h.1.indexLocal h.1.capLocal byte h.1.usedLocal loaded occupied
  refine ⟨result,post,?_,outcome,ticks,?_,memory,globals,code,domain,endian⟩
  · cases result <;> exact run
  · intro continuing
    have nextInside : (hashProbeNext probe capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat probe capacity bits arrays.power inside]
      apply Nat.mod_lt
      rw [arrays.power]
      exact Nat.two_pow_pos bits
    exact ⟨h.1.preserve 52 keys stride key capacity used empty current post probe _ nextInside memory code domain endian (locals continuing),
      h.2.after_read current post 52 table keys stride capacity used values order orderPos count bits memory code domain endian⟩

#print axioms evaluate_hashFind_table_loop52
end InitECandidate.Runtime
