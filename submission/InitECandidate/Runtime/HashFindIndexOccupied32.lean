import InitECandidate.Runtime.HashFindIndex32
import InitECandidate.Runtime.HashFindTailOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_hashFindIndexScope32_occupied {F : Type} (keys stride key capacity used empty hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (state : PanSemStateFiniteExact 64 F)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (valid : HashFindInvariant32 keys stride key capacity used empty
      (setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state)
      (hashFindInitialIndex hash capacity))
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      (found ≠ capacity → hashOccupancyRead post used found ≠ some 0) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state
  obtain ⟨found,post,run,inside,occupied,cost,remaining,memory,globals,code,addresses,endian⟩ := evaluate_hashFindTail32_occupied keys stride key capacity used empty bits
    power emptyInside keysAligned strideAligned keyAligned strideFits bounded entered _ valid budget
  unfold hashFindIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (hashFindInitialIndex hash capacity)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]
  exact ⟨found,_,rfl,inside,occupied,cost,remaining,memory,globals,code,addresses,endian⟩

#print axioms evaluate_hashFindIndexScope32_occupied
end InitECandidate.Runtime
