import InitECandidate.Runtime.HtrRequestListStepBound
import InitECandidate.Runtime.RankedWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HtrRequestListState (kind pointer size roots heap count : BitVec 64)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop where
  heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer))
  kindLocal : state.locals.lookup (ofString "kind") = some (.val (.word kind))
  sizeLocal : state.locals.lookup (ofString "sz") = some (.val (.word size))
  rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots))
  countLocal : state.locals.lookup (ofString "n") = some (.val (.word count))
  cursor : ∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    index.toNat ≤ count.toNat ∧ count.toNat - index.toNat ≤ rank

theorem htrRequestList_loop_ranked (kind pointer size roots heap count : BitVec 64)
    (countBound : count.toNat ≤ 134217712) (heapFits : heap.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      HtrRequestListState kind pointer size roots heap count state rank →
      rank * (htrRequestStepCost + 1) ≤ state.clock →
      RankedOutcome state htrRequestListCondition (rank * (htrRequestStepCost + 1))
        (HtrRequestListState kind pointer size roots heap count) False
        (evaluateHOLFiniteState state (.while htrRequestListCondition htrRequestListStep)) := by
  refine rankedWhile_run htrRequestListCondition htrRequestListStep (htrRequestStepCost)
    (HtrRequestListState kind pointer size roots heap count) False ?_ ?_
  · intro F state valid flag guard
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "n") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrRequestListCondition = _ at condition
    rw [condition] at guard
    have stopped : ¬ index.toNat < count.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank flag code valid guard nonzero budget
    obtain ⟨index,atIndex,within,remaining⟩ := valid.cursor
    have condition := eval_localBound_less state (ofString "i") (ofString "n") .less (Or.inl rfl)
      index count (by omega) (by omega) atIndex valid.countLocal
    change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrRequestListCondition = _ at condition
    have running : index.toNat < count.toNat := by
      by_contra stopped
      rw [condition] at guard
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : htrRequestStepCost ≤ (decClockHOLFinite state).clock := by
      change htrRequestStepCost ≤ state.clock - 1
      omega
    have bounded := htrRequestList_step_bound (decClockHOLFinite state) kind pointer index size roots heap
      ⟨valid.kindLocal,valid.pointerLocal,atIndex,valid.sizeLocal,valid.rootsLocal⟩ valid.heapGlobal heapFits code enough
    refine ⟨bounded.1.1,bounded.1.2.1,bounded.1.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) htrRequestListStep with
        | mk result post =>
          rw [bodyRun] at normal
          dsimp only at normal
          subst normal
          have facts := bounded.2 post bodyRun
          have natural : (index + (1#64)).toNat = index.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
            rfl
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) htrRequestListStep
          rw [bodyRun] at metadata
          refine ⟨count.toNat - (index + (1#64)).toNat,by rw [natural]; omega,?_,metadata.1⟩
          exact {
            heapGlobal := facts.1
            pointerLocal := (facts.2.2 _ (by decide)).trans valid.pointerLocal
            kindLocal := (facts.2.2 _ (by decide)).trans valid.kindLocal
            sizeLocal := (facts.2.2 _ (by decide)).trans valid.sizeLocal
            rootsLocal := (facts.2.2 _ (by decide)).trans valid.rootsLocal
            countLocal := (facts.2.2 _ (by decide)).trans valid.countLocal
            cursor := ⟨index + (1#64),facts.2.1,by rw [natural]; omega,Nat.le_refl _⟩ }
      · exact absurd cont (evaluate_noTopContinue htrRequestListStep (by decide) (decClockHOLFinite state))
    · intro broken
      exact absurd broken (evaluate_noTopBreak htrRequestListStep (by decide) (decClockHOLFinite state))


theorem runBounded_htrRequestList_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer size roots heap count : BitVec 64) (rank : Nat)
    (countBound : count.toNat ≤ 134217712) (heapFits : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode)
    (valid : HtrRequestListState kind pointer size roots heap count state rank)
    (budget : rank * (htrRequestStepCost + 1) ≤ state.clock) :
    RunBounded state (.while htrRequestListCondition htrRequestListStep)
      (rank * (htrRequestStepCost + 1)) := by
  have loop := htrRequestList_loop_ranked kind pointer size roots heap count countBound heapFits rank state code valid budget
  exact ⟨loop.1,loop.2.1,loop.2.2.1⟩

#print axioms runBounded_htrRequestList_loop
#print axioms htrRequestList_loop_ranked
end InitECandidate.Runtime
