import InitECandidate.Runtime.CeilLog2InputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The three byte lengths used by original merkleize are natural, partition
the allocated buffer, and are within the proven memory-helper size domain. -/
def MerkleChunkLengths (n size : BitVec 64) : Prop :=
  n.toNat ≤ size.toNat ∧ size.toNat ≤ 134217728 ∧
    (size * (32#64)).toNat = size.toNat * 32 ∧
    (n * (32#64)).toNat = n.toNat * 32 ∧
    ((size - n) * (32#64)).toNat = (size.toNat - n.toNat) * 32 ∧
    (size * (32#64)).toNat ≤ 4294967296 ∧
    (n * (32#64)).toNat ≤ 4294967296 ∧
    ((size - n) * (32#64)).toNat ≤ 4294967296 ∧
    (n * (32#64)).toNat + ((size - n) * (32#64)).toNat = (size * (32#64)).toNat

theorem merkleChunkLengths_of_bounds (n size : BitVec 64)
    (covers : n.toNat ≤ size.toNat) (small : size.toNat ≤ 134217728) :
    MerkleChunkLengths n size := by
  have total : size.toNat * 32 ≤ 4294967296 := by omega
  have totalNatural : (size * (32#64)).toNat = size.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change size.toNat * 32 < 2 ^ 64; omega)]
    rfl
  have copiedNatural : (n * (32#64)).toNat = n.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change n.toNat * 32 < 2 ^ 64; omega)]
    rfl
  have difference : (size - n).toNat = size.toNat - n.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr covers)
  have zeroedNatural : ((size - n) * (32#64)).toNat = (size.toNat - n.toNat) * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change (size - n).toNat * 32 < 2 ^ 64; rw [difference]; omega)]
    change (size - n).toNat * 32 = _
    rw [difference]
  refine ⟨covers,small,totalNatural,copiedNatural,zeroedNatural,?_,?_,?_,?_⟩
  all_goals simp only [totalNatural,copiedNatural,zeroedNatural]
  all_goals omega

/-- The original ceil-log return, specialized to the checked input limit,
supplies all three actual merkleize byte-length bounds. -/
theorem merkleChunkLengths_of_ceilLog2_returned {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (n : BitVec 64) (value : ValueHOL 64)
    (input : state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "n") = some (.val (.word n)))
    (small : n.toNat ≤ 134217712)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ceil_log2) =
      (some (.returned value),post)) :
    ∃ d : BitVec 64, value = .val (.word d) ∧ d.toNat ≤ 27 ∧
      MerkleChunkLengths n ((1#64) <<< d.toNat) := by
  obtain ⟨d,valueEq,bounded,covers,sizeBound⟩ := ceilLog2_body_input_bound state post n value input small run
  exact ⟨d,valueEq,bounded,merkleChunkLengths_of_bounds n _ covers sizeBound⟩

#print axioms merkleChunkLengths_of_bounds
#print axioms merkleChunkLengths_of_ceilLog2_returned
end InitECandidate.Runtime
