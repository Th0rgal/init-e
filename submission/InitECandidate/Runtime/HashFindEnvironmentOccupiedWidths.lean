import InitECandidate.Runtime.HashFindIndexOccupiedWidths
import InitECandidate.Runtime.HashFindEnvironmentWidths
import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindIndexScope20_from_count_occupied {F : Type} (table keys stride capacity used values order orderPos count key hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 20 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) ready.room
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have valid : HashFindInvariant 20 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyWords,ready.keyBytes,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope20_occupied table keys stride capacity used values order orderPos count key empty hash
    bits power emptyInside keyAligned state hashLocal ready.capLocal valid arrays budget

theorem evaluate_hashFindIndexScope52_from_count_occupied {F : Type} (table keys stride capacity used values order orderPos count key hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment 52 keys stride key capacity used state)
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨empty,emptyInside,emptyLoad⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used) ready.room
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have valid : HashFindInvariant 52 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyWords,ready.keyBytes,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope52_occupied table keys stride capacity used values order orderPos count key empty hash
    bits power emptyInside keyAligned state hashLocal ready.capLocal valid arrays budget

#print axioms evaluate_hashFindIndexScope20_from_count_occupied
#print axioms evaluate_hashFindIndexScope52_from_count_occupied
end InitECandidate.Runtime
