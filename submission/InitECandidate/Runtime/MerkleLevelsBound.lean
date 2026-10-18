import InitECandidate.Runtime.MerkleLevelBound
import InitECandidate.Runtime.MerkleLevelReturned
import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def merkleLevelsCondition : ExpHOL 64 :=
  .cmp .less (.const 1) (.var .local (ofString "cur"))

def MerkleLevelRank {F : Type} (state : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ cur : BitVec 64, state.locals.lookup (ofString "cur") = some (.val (.word cur)) ∧
    cur.toNat < 2 ^ 63 ∧ cur.toNat ≤ n

theorem eval_merkleLevels_condition {F : Type} (state : PanSemStateFiniteExact 64 F)
    (cur : BitVec 64) (counter : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (small : cur.toNat < 2 ^ 63) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) merkleLevelsCondition =
      some (.val (.word (if 1 < cur.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  simp only [merkleLevelsCondition,evalHOLExact,counter,Compiler.Encoders.Asm.wordCmpHOL,
    holAsmSignedLess_small (1 : BitVec 64) cur (by decide) small]
  by_cases less : 1 < cur.toNat <;> simp [less]

/-- The original outer Merkle loop decreases the actual chunk count after
every completed level. Rejections and external exits are bounded too. -/
theorem merkleLevels_ranked :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → MerkleLevelRank state n →
      n * (merkleLevelCost + 1) ≤ state.clock →
      RankedOutcome state merkleLevelsCondition (n * (merkleLevelCost + 1)) MerkleLevelRank False
        (evaluateHOLFiniteState state (.while merkleLevelsCondition merkleLevelBody)) := by
  refine rankedWhile_run merkleLevelsCondition merkleLevelBody merkleLevelCost MerkleLevelRank False ?_ ?_
  · intro F state ranked word guard
    obtain ⟨cur,counter,small,zero⟩ := ranked
    rw [eval_merkleLevels_condition state cur counter small] at guard
    have notLess : ¬ 1 < cur.toNat := by omega
    simpa [notLess] using guard.symm
  · intro F state n word code ranked guard running budget
    obtain ⟨cur,counter,small,within⟩ := ranked
    have condition := eval_merkleLevels_condition state cur counter small
    have positive : 1 < cur.toNat := by
      by_contra notPositive
      rw [condition] at guard
      have zero : word = (0 : BitVec 64) := by simpa [notPositive] using guard.symm
      exact running zero
    have bounded := merkleLevel_body_bounded (decClockHOLFinite state) code
      (by change merkleLevelCost ≤ state.clock - 1; omega)
    have noCont := evaluate_noTopContinue merkleLevelBody (by decide) (decClockHOLFinite state)
    have noBreak := evaluate_noTopBreak merkleLevelBody (by decide) (decClockHOLFinite state)
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
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

#print axioms eval_merkleLevels_condition
#print axioms merkleLevels_ranked
end InitECandidate.Runtime
