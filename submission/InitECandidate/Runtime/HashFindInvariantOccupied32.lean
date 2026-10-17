import InitECandidate.Runtime.HashFindInvariant32
import InitECandidate.Runtime.HashFindLoopRankOccupied
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_hashFindLoop32_occupied {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * hashProbeDistance capacity.toNat index.toNat empty.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ hashOccupancyRead post used found ≠ some 0 ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant32 keys stride key capacity used empty post finalIndex) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  apply evaluate_hashFindLoop_rank_occupied capacity empty used bits power emptyInside
    (HashFindInvariant32 keys stride key capacity used empty)
    (fun _ _ h => ⟨h.indexLocal,h.usedLocal⟩)
    (fun _ _ h => h.readable _ h.inside) (fun _ _ h => h.emptyLoad) ?_
    _ state index valid valid.inside rfl budget
  intro current probe byte h inside enough loaded occupied
  obtain ⟨result,post,run,outcome,ticks,memory,globals,code,addresses,endian,_,locals⟩ :=
    evaluate_hashFind_occupied32 current keys stride key probe capacity used byte h.code enough
      keysAligned strideAligned keyAligned strideFits inside bounded h.arrayDomain h.keyDomain
      h.keysLocal h.strideLocal h.keyLocal h.lengthLocal h.indexLocal h.capLocal h.usedLocal loaded occupied
  refine ⟨result,post,?_,outcome,ticks,?_,memory,globals,code,addresses,endian⟩
  · cases result <;> exact run
  · intro continuing
    have nextInside : (hashProbeNext probe capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat probe capacity bits power inside]
      apply Nat.mod_lt
      rw [power]; exact Nat.two_pow_pos bits
    exact HashFindInvariant32.preserve keys stride key capacity used empty current post probe _ h nextInside memory code addresses endian (locals continuing)

theorem evaluate_hashFindLoop32_capacity_occupied {F : Type} (keys stride key capacity used empty : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant32 keys stride key capacity used empty state index)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ hashOccupancyRead post used found ≠ some 0 ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant32 keys stride key capacity used empty post finalIndex) ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat valid.inside emptyInside
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ := evaluate_hashFindLoop32_occupied keys stride key capacity used empty bits
    power emptyInside keysAligned strideAligned keyAligned strideFits bounded state index valid (by omega)
  exact ⟨result,post,run,by omega,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩

#print axioms evaluate_hashFindLoop32_occupied
#print axioms evaluate_hashFindLoop32_capacity_occupied
end InitECandidate.Runtime
