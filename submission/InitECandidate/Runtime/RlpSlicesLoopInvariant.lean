import InitECandidate.Runtime.RlpSlicesStepInvariant
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Only loop-control locals are needed for a runtime bound: unreadable
input or failed output stores exit, and do not require memory invariants. -/
structure RlpSlicesLoopWitness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64) where
  offset : BitVec 64
  index : BitVec 64
  pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer))
  countLocal : state.locals.lookup (ofString "count") = some (.val (.word count))
  offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset))
  indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))
  indexBound : index.toNat ≤ count.toNat
  code : state.code = originalRuntimeCode

def RlpSlicesLoopWitness.decClock {F : Type} {state : PanSemStateFiniteExact 64 F}
    {pointer count : BitVec 64} (valid : RlpSlicesLoopWitness state pointer count) :
    RlpSlicesLoopWitness (decClockHOLFinite state) pointer count :=
  ⟨valid.offset,valid.index,valid.pointerLocal,valid.countLocal,valid.offsetLocal,valid.indexLocal,valid.indexBound,valid.code⟩

def rlpSlicesRank {F : Type} (count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => count.toNat - index.toNat
  | _ => 0

theorem rlpSlices_rank_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer count : BitVec 64)
    (valid : RlpSlicesLoopWitness state pointer count) :
    rlpSlicesRank count state = count.toNat - valid.index.toNat := by
  simp [rlpSlicesRank,valid.indexLocal]

/-- Successful actual iterations retain the complete runtime witness and
strictly lower the remaining-slice rank. -/
theorem rlpSlices_loop_witness_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64) (valid : RlpSlicesLoopWitness state pointer count)
    (enabled : 0 < rlpSlicesRank count state)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ _next : RlpSlicesLoopWitness post pointer count, rlpSlicesRank count post < rlpSlicesRank count state := by
  have inside : valid.index.toNat < count.toNat := by
    rw [rlpSlices_rank_eq state pointer count valid] at enabled
    omega
  obtain ⟨offset,offsetLocal,indexLocal,countLocal,pointerLocal,indexBound,decreases⟩ :=
    rlpSlices_step_normal_invariant state post pointer valid.offset valid.index count valid.pointerLocal valid.offsetLocal
      valid.indexLocal valid.countLocal inside valid.code run
  have metadata := evaluateHOLFiniteState_metadata state rlpSlicesStep
  rw [run] at metadata
  let next : RlpSlicesLoopWitness post pointer count :=
    ⟨offset,valid.index+1,pointerLocal,countLocal,offsetLocal,indexLocal,indexBound,metadata.1.trans valid.code⟩
  refine ⟨next,?_⟩
  rw [rlpSlices_rank_eq post pointer count next,rlpSlices_rank_eq state pointer count valid]
  exact decreases

#print axioms rlpSlices_loop_witness_step
end InitECandidate.Runtime
