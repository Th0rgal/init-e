import InitECandidate.Runtime.HashTableArraysRead
import InitECandidate.Runtime.HashFindIndex32
import InitECandidate.Runtime.HashFindTailWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFindIndexScope20 {F : Type} (table keys stride capacity used values order orderPos count key empty hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (valid : HashFindInvariant 20 keys stride key capacity used empty
      (setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state)
      (hashFindInitialIndex hash capacity))
    (arrays : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state
  obtain ⟨found,post,run,inside,cost,remaining,memory,globals,code,addresses,endian⟩ := evaluate_hashFindTail20
    table keys stride capacity used values order orderPos count key empty bits
    emptyInside keyAligned entered _ valid (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) budget
  unfold hashFindIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (hashFindInitialIndex hash capacity)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]
  exact ⟨found,_,rfl,inside,cost,remaining,memory,globals,code,addresses,endian⟩


theorem evaluate_hashFindIndexScope52 {F : Type} (table keys stride capacity used values order orderPos count key empty hash : BitVec 64)
    (bits : Nat) (power : capacity.toNat = 2 ^ bits) (emptyInside : empty.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (state : PanSemStateFiniteExact 64 F)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (valid : HashFindInvariant 52 keys stride key capacity used empty
      (setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state)
      (hashFindInitialIndex hash capacity))
    (arrays : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (budget : 2 * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state
  obtain ⟨found,post,run,inside,cost,remaining,memory,globals,code,addresses,endian⟩ := evaluate_hashFindTail52
    table keys stride capacity used values order orderPos count key empty bits
    emptyInside keyAligned entered _ valid (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) budget
  unfold hashFindIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (hashFindInitialIndex hash capacity)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]
  exact ⟨found,_,rfl,inside,cost,remaining,memory,globals,code,addresses,endian⟩


#print axioms evaluate_hashFindIndexScope20
#print axioms evaluate_hashFindIndexScope52
end InitECandidate.Runtime
