import InitECandidate.Runtime.PtKeyUFindGD
import InitECandidate.Runtime.HashFindIndexWidths
/-!
Lookup tail and index scope at any key alignment, bounded by `(n + 2)` times the capacity.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ft
variable {F : Type}

theorem evaluate_hashFind_table_loopK_capacity
    (n table keys stride capacity used values order orderPos count key empty : BitVec 64) (bits : Nat)
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (emptyInside : empty.toNat < capacity.toNat)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant n keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (budget : (n.toNat + 2) * capacity.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop = (result,post) ∧
      state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat ∧
      post.clock ≤ state.clock ∧ (result = none ∨ ∃ found : BitVec 64,
        found.toNat < capacity.toNat ∧ result = some (.returned (.val (.word found)))) ∧
      (result = none → ∃ finalIndex, HashFindInvariant n keys stride key capacity used empty post finalIndex ∧
        HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits post) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have rankBound := hashProbeDistance_lt_capacity capacity.toNat index.toNat empty.toNat valid.inside emptyInside
  have scaled := Nat.mul_le_mul_left (n.toNat + 2) (Nat.le_of_lt rankBound)
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,domain,endian⟩ :=
    evaluate_hashFind_table_loopK n table keys stride capacity used values order orderPos count key empty bits sup keyFit
      emptyInside state index valid arrays (by omega)
  exact ⟨result,post,run,by omega,remaining,outcome,finalInvariant,memory,globals,code,domain,endian⟩

theorem evaluate_hashFindTailK (n table keys stride capacity used values order orderPos count key empty : BitVec 64)
    (bits : Nat) (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (emptyInside : empty.toNat < capacity.toNat)
    (state : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (valid : HashFindInvariant n keys stride key capacity used empty state index)
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (budget : (n.toNat + 2) * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindTail =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨result,post,run,cost,remaining,outcome,finalInvariant,memory,globals,code,addresses,endian⟩ :=
    evaluate_hashFind_table_loopK_capacity n table keys stride capacity used values order orderPos count key empty bits
      sup keyFit emptyInside state index valid arrays budget
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

theorem evaluate_hashFindIndexScopeK (n table keys stride capacity used values order orderPos count key empty hash : BitVec 64)
    (bits : Nat) (sup : n = 20 ∨ n = 32 ∨ n = 52) (keyFit : key.toNat + n.toNat < 2 ^ 64)
    (emptyInside : empty.toNat < capacity.toNat)
    (state : PanSemStateFiniteExact 64 F)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (valid : HashFindInvariant n keys stride key capacity used empty
      (setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state)
      (hashFindInitialIndex hash capacity))
    (arrays : HashTableArraysInvariant n table keys stride capacity used values order orderPos count bits state)
    (budget : (n.toNat + 2) * capacity.toNat ≤ state.clock) :
    ∃ found : BitVec 64, ∃ post, evaluateHOLFiniteState state hashFindIndexScope =
        (some (.returned (.val (.word found))),post) ∧ found.toNat ≤ capacity.toNat ∧
      state.clock ≤ post.clock + (n.toNat + 2) * capacity.toNat ∧ post.clock ≤ state.clock ∧ post.memory = state.memory ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state
  obtain ⟨found,post,run,inside,cost,remaining,memory,globals,code,addresses,endian⟩ := evaluate_hashFindTailK
    n table keys stride capacity used values order orderPos count key empty bits sup keyFit
    emptyInside entered _ valid (HashTableArraysInvariant.after_read state entered _ _ _ _ _ _ _ _ _ _ bits arrays rfl rfl rfl rfl) budget
  unfold hashFindIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (hashFindInitialIndex hash capacity)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]
  exact ⟨found,_,rfl,inside,cost,remaining,memory,globals,code,addresses,endian⟩

end ft
#print axioms evaluate_hashFindTailK
#print axioms evaluate_hashFindIndexScopeK
end InitECandidate.Runtime
