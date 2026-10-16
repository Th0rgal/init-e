import InitECandidate.Runtime.HashFindTail32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashFindInitialIndex (hash capacity : BitVec 64) : BitVec 64 := hash &&& (capacity - 1)

def hashFindIndexExpression : ExpHOL 64 :=
  .op .and [.var .local (ofString "h"),.op .sub [.var .local (ofString "cap"),.const 1]]

/-- An arbitrary64-bit hash is masked into a power-of-two table's range. -/
theorem hashFind_initial_index_bound (hash capacity : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) :
    (hashFindInitialIndex hash capacity).toNat = hash.toNat % capacity.toNat ∧
      (hashFindInitialIndex hash capacity).toNat < capacity.toNat := by
  have positive : 0 < capacity.toNat := by rw [power]; exact Nat.two_pow_pos bits
  have oneLe : (1 : BitVec 64) ≤ capacity := BitVec.le_def.mpr (by change 1 ≤ capacity.toNat; omega)
  have decrement : (capacity - 1).toNat = capacity.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le oneLe]; rfl
  have exactIndex : (hashFindInitialIndex hash capacity).toNat = hash.toNat % capacity.toNat := by
    simp only [hashFindInitialIndex,BitVec.toNat_and,decrement]
    rw [power,Nat.and_two_pow_sub_one_eq_mod]
  exact ⟨exactIndex,by rw [exactIndex]; exact Nat.mod_lt _ positive⟩

theorem eval_hashFind_initial_index {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hash capacity : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      hashFindIndexExpression = some (.val (.word (hashFindInitialIndex hash capacity))) := by
  simp [hashFindIndexExpression,evalHOLExact,evalListHOLExact,hashLocal,capLocal,wordOpHOL,wordOp,
    valueIsWord,valueWord,hashFindInitialIndex]
  change hash &&& ((capacity - 1) &&& BitVec.allOnes 64) = _
  rw [BitVec.and_allOnes]
  rfl

def hashFindIndexScope : ProgHOL 64 :=
  .dec (ofString "i") .one hashFindIndexExpression hashFindTail

theorem source_htabFind_index_scope :
    sourceFindLocalScope (ofString "i") (sourceFunctionBody Guest.guestFn_htab_find_slot) =
      some hashFindIndexScope := source_htabFind_tail

/-- Actual probe-index declaration, complete loop and final sentinel return.
The declaration adds no clocks and restores its saved local on either return. -/
theorem evaluate_hashFindIndexScope32 {F : Type} (keys stride key capacity used empty hash : BitVec 64)
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
      state.clock ≤ post.clock + 2 * capacity.toNat ∧ post.clock ≤ state.clock := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (hashFindInitialIndex hash capacity))) state
  obtain ⟨found,post,run,inside,cost,remaining⟩ := evaluate_hashFindTail32 keys stride key capacity used empty bits
    power emptyInside keysAligned strideAligned keyAligned strideFits bounded entered _ valid budget
  unfold hashFindIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (hashFindInitialIndex hash capacity)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,run]
  exact ⟨found,_,rfl,inside,cost,remaining⟩

#print axioms hashFind_initial_index_bound
#print axioms eval_hashFind_initial_index
#print axioms source_htabFind_index_scope
#print axioms evaluate_hashFindIndexScope32
end InitECandidate.Runtime
