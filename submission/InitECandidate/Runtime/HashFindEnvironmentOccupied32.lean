import InitECandidate.Runtime.HashFindEnvironment32
import InitECandidate.Runtime.HashFindIndexOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_hashFindIndexScope32_from_count_occupied {F : Type} (keys stride key capacity used hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F) (ready : HashFindEnvironment32 keys stride key capacity used state)
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
  have valid : HashFindInvariant32 keys stride key capacity used empty entered index := by
    refine ⟨ready.code,(hashFind_initial_index_bound hash capacity bits power).2,?_,?_,?_,?_,?_,?_,?_,
      ready.arrayDomain,ready.keyDomain,ready.readable,emptyLoad⟩
    · rw [other _ (by decide)]; exact ready.keysLocal
    · rw [other _ (by decide)]; exact ready.strideLocal
    · rw [other _ (by decide)]; exact ready.keyLocal
    · rw [other _ (by decide)]; exact ready.lengthLocal
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [other _ (by decide)]; exact ready.capLocal
    · rw [other _ (by decide)]; exact ready.usedLocal
  exact evaluate_hashFindIndexScope32_occupied keys stride key capacity used empty hash bits power emptyInside keysAligned strideAligned
    keyAligned strideFits bounded state hashLocal ready.capLocal valid budget

#print axioms evaluate_hashFindIndexScope32_from_count_occupied
end InitECandidate.Runtime
