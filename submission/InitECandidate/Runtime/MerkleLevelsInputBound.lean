import InitECandidate.Runtime.MerkleLevelsBound
import InitECandidate.Runtime.MerkleLevelInputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def MerkleInputRank (upper : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ cur : BitVec 64, state.locals.lookup (ofString "cur") = some (.val (.word cur)) ∧
    cur.toNat ≤ upper ∧ cur.toNat ≤ n

/-- An input-sized constant bounds every level, while halving decreases the
outer rank. This gives a quadratic bound in the initial chunk-count ceiling. -/
theorem merkleLevels_input_ranked (upper : Nat) (smallUpper : upper < 2 ^ 63) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → MerkleInputRank upper state n →
      n * (upper * 137 + 1) ≤ state.clock →
      RankedOutcome state merkleLevelsCondition (n * (upper * 137 + 1)) (MerkleInputRank upper) False
        (evaluateHOLFiniteState state (.while merkleLevelsCondition merkleLevelBody)) := by
  refine rankedWhile_run merkleLevelsCondition merkleLevelBody (upper * 137) (MerkleInputRank upper) False ?_ ?_
  · intro F state ranked word guard
    obtain ⟨cur,counter,bounded,zero⟩ := ranked
    rw [eval_merkleLevels_condition state cur counter (by omega)] at guard
    have notLess : ¬ 1 < cur.toNat := by omega
    simpa [notLess] using guard.symm
  · intro F state n word code ranked guard running budget
    obtain ⟨cur,counter,bounded,within⟩ := ranked
    have condition := eval_merkleLevels_condition state cur counter (by omega)
    have positive : 1 < cur.toNat := by
      by_contra notPositive
      rw [condition] at guard
      have zero : word = (0 : BitVec 64) := by simpa [notPositive] using guard.symm
      exact running zero
    have allocated : cur.toNat * 137 ≤ upper * 137 := Nat.mul_le_mul_right _ bounded
    have bodyBound := runBounded_merkleLevel (decClockHOLFinite state) cur counter (by omega) code
      (by change cur.toNat * 137 ≤ state.clock - 1; omega)
    have weakened := bodyBound.weaken allocated
    have noCont := evaluate_noTopContinue merkleLevelBody (by decide) (decClockHOLFinite state)
    have noBreak := evaluate_noTopBreak merkleLevelBody (by decide) (decClockHOLFinite state)
    refine ⟨weakened.1,weakened.2.1,weakened.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases run : evaluateHOLFiniteState (decClockHOLFinite state) merkleLevelBody with
        | mk result post =>
          rw [run] at normal
          dsimp only at normal
          subst normal
          have nextCounter := merkleLevel_body_normal (decClockHOLFinite state) post cur counter run
          have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) merkleLevelBody
          rw [run] at meta'
          have natural : (cur >>> 1).toNat = cur.toNat / 2 := by
            simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
          have decreases : (cur >>> 1).toNat < cur.toNat := by
            rw [natural]
            exact Nat.div_lt_self (by omega) (by decide)
          exact ⟨n,le_refl _,⟨cur >>> 1,nextCounter,by omega,by omega⟩,meta'.1⟩
      · exact absurd cont noCont
    · intro broken
      exact absurd broken noBreak

def merkleInputTreeCost : Nat := 134217728 * (134217728 * 137 + 1)

theorem runBounded_merkleInputLevels {F : Type} (state : PanSemStateFiniteExact 64 F)
    (cur : BitVec 64) (counter : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (bounded : cur.toNat ≤ 134217728) (code : state.code = originalRuntimeCode)
    (budget : merkleInputTreeCost ≤ state.clock) :
    RunBounded state (.while merkleLevelsCondition merkleLevelBody) merkleInputTreeCost := by
  have loop := merkleLevels_input_ranked 134217728 (by decide) 134217728 state code
    ⟨cur,counter,bounded,bounded⟩ budget
  exact ⟨loop.1,loop.2.1,loop.2.2.1⟩

#print axioms merkleLevels_input_ranked
#print axioms runBounded_merkleInputLevels
end InitECandidate.Runtime
