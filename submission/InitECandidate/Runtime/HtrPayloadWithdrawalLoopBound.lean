import InitECandidate.Runtime.HtrPayloadWithdrawalStepReturned
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrPayloadWithdrawalState (array roots heap count : BitVec 64)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop where
  heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array))
  rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots))
  countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count))
  cursor : ∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    index.toNat ≤ count.toNat ∧ count.toNat - index.toNat ≤ rank

theorem htrPayload_withdrawal_loop_ranked (array roots heap count : BitVec 64)
    (countBound : count.toNat ≤ 134217712) (heapFits : heap.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      HtrPayloadWithdrawalState array roots heap count state rank →
      rank * (htrWithdrawalBodyCost + 2) ≤ state.clock →
      RankedOutcome state htrPayloadWithdrawalCondition (rank * (htrWithdrawalBodyCost + 2))
        (HtrPayloadWithdrawalState array roots heap count) False
        (evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep)) := by
  refine rankedWhile_run htrPayloadWithdrawalCondition htrPayloadWithdrawalStep (htrWithdrawalBodyCost + 1)
    (HtrPayloadWithdrawalState array roots heap count) False ?_ ?_
  · intro F state valid flag guard
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "nwd") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalCondition = _ at condition
    rw [condition] at guard
    have stopped : ¬ index.toNat < count.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank flag code valid guard nonzero budget
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "nwd") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalCondition = _ at condition
    have running : index.toNat < count.toNat := by
      by_contra stopped
      rw [condition] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : htrWithdrawalBodyCost + 1 ≤ (decClockHOLFinite state).clock := by
      change htrWithdrawalBodyCost + 1 ≤ state.clock - 1
      omega
    have bounded := runBounded_htrPayload_withdrawal_step (decClockHOLFinite state) array index roots heap
      valid.arrayLocal atIndex valid.rootsLocal valid.heapGlobal heapFits code enough
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) htrPayloadWithdrawalStep with
        | mk result post =>
          rw [bodyRun] at normal
          dsimp only at normal
          subst normal
          have facts := htrPayload_withdrawal_step_normal (decClockHOLFinite state) post array index roots heap
            valid.arrayLocal atIndex valid.rootsLocal valid.heapGlobal code bodyRun
          have natural : (index + (1#64)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
            rfl
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) htrPayloadWithdrawalStep
          rw [bodyRun] at metadata
          refine ⟨count.toNat - (index + (1#64)).toNat,by rw [natural]; omega,?_,metadata.1⟩
          exact {
            heapGlobal := by rw [facts.1]; exact valid.heapGlobal
            arrayLocal := (facts.2.2 _ (by decide)).trans valid.arrayLocal
            rootsLocal := (facts.2.2 _ (by decide)).trans valid.rootsLocal
            countLocal := (facts.2.2 _ (by decide)).trans valid.countLocal
            cursor := ⟨index + (1#64),facts.2.1,by rw [natural]; omega,Nat.le_refl _⟩ }
      · exact absurd cont (evaluate_noTopContinue htrPayloadWithdrawalStep (by decide) (decClockHOLFinite state))
    · intro broken
      exact absurd broken (evaluate_noTopBreak htrPayloadWithdrawalStep (by decide) (decClockHOLFinite state))


theorem runBounded_htrPayload_withdrawal_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array roots heap count : BitVec 64) (rank : Nat)
    (countBound : count.toNat ≤ 134217712) (heapFits : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (budget : rank * (htrWithdrawalBodyCost + 2) ≤ state.clock) :
    RunBounded state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep)
      (rank * (htrWithdrawalBodyCost + 2)) := by
  have loop := htrPayload_withdrawal_loop_ranked array roots heap count countBound heapFits rank state code valid budget
  exact ⟨loop.1,loop.2.1,loop.2.2.1⟩

#print axioms runBounded_htrPayload_withdrawal_loop
#print axioms htrPayload_withdrawal_loop_ranked
end InitECandidate.Runtime
