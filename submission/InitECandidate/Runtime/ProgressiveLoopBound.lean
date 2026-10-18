import InitECandidate.Runtime.ProgressiveRank
import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_progressive_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (off n : BitVec 64)
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) progressiveCondition =
      some (.val (.word (if off.toNat < n.toNat then 1 else 0))) := by
  simp [progressiveCondition,evalHOLExact,ho,hn,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

theorem progressive_loop_ranked (p n roots heap : BitVec 64)
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → ProgressiveRank p n roots heap state rank →
      rank * (merkleBodyCost + 2) ≤ state.clock →
      RankedOutcome state progressiveCondition (rank * (merkleBodyCost + 2))
        (ProgressiveRank p n roots heap) False
        (evaluateHOLFiniteState state (.while progressiveCondition progressiveStep)) := by
  refine rankedWhile_run progressiveCondition progressiveStep (merkleBodyCost + 1)
    (ProgressiveRank p n roots heap) False ?_ ?_
  · intro F state ranked word guard
    obtain ⟨hp,hn,hr,hh,off,size,k,ho,hs,hk,counters,bound⟩ := ranked
    rw [eval_progressive_condition state off n ho hn] at guard
    have stopped : ¬ off.toNat < n.toNat := by omega
    simpa [stopped] using guard.symm
  · intro F state rank word code ranked guard running budget
    obtain ⟨hp,hn,hr,hh,off,size,k,ho,hs,hk,counters,bound⟩ := ranked
    have positive : off.toNat < n.toNat := by
      by_contra stopped
      rw [eval_progressive_condition state off n ho hn] at guard
      exact running (by simpa [stopped] using guard.symm)
    have bodyBound := runBounded_progressive_step (decClockHOLFinite state) p n off size roots k heap
      hp hn ho hs hr hk small (by omega) hh heapBound code
      (by change merkleBodyCost + 1 ≤ state.clock - 1; omega)
    have noCont := evaluate_noTopContinue progressiveStep (by decide) (decClockHOLFinite state)
    have noBreak := evaluate_noTopBreak progressiveStep (by decide) (decClockHOLFinite state)
    refine ⟨bodyBound.1,bodyBound.2.1,bodyBound.2.2,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases run : evaluateHOLFiniteState (decClockHOLFinite state) progressiveStep with
        | mk result post =>
          rw [run] at normal
          dsimp only at normal
          subst normal
          have rankedBefore : ProgressiveRank p n roots heap (decClockHOLFinite state) (rank + 1) :=
            ⟨hp,hn,hr,hh,off,size,k,ho,hs,hk,counters,bound⟩
          obtain ⟨nextRank,decreased,rankedNext⟩ := progressive_rank_normal (decClockHOLFinite state) post
            p n roots heap (rank + 1) small rankedBefore (by
              intro candidate atCandidate
              change state.locals.lookup (ofString "off") = some (.val (.word candidate)) at atCandidate
              have same : candidate = off := by simpa [ho] using atCandidate.symm
              subst candidate
              exact positive) code run
          have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) progressiveStep
          rw [run] at meta'
          exact ⟨nextRank,by omega,rankedNext,meta'.1⟩
      · exact absurd cont noCont
    · intro broken
      exact absurd broken noBreak

theorem runBounded_progressive_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64) (rank : Nat)
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (valid : ProgressiveRank p n roots heap state rank)
    (budget : rank * (merkleBodyCost + 2) ≤ state.clock) :
    RunBounded state (.while progressiveCondition progressiveStep) (rank * (merkleBodyCost + 2)) := by
  have loop := progressive_loop_ranked p n roots heap small heapBound rank state code valid budget
  exact ⟨loop.1,loop.2.1,loop.2.2.1⟩

theorem progressive_initial_rank {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word (0#64))))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word (1#64))))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word (0#64)))) :
    ProgressiveRank p n roots heap state n.toNat := by
  exact ⟨hp,hn,hr,hh,0,1,0,ho,hs,hk,progressive_counters_initial n,by simp⟩

theorem progressive_loop_normal_k_bound {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64) (rank : Nat)
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (valid : ProgressiveRank p n roots heap state rank)
    (budget : rank * (merkleBodyCost + 2) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while progressiveCondition progressiveStep) = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      ∃ k : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word k)) ∧ k.toNat ≤ 4 * n.toNat := by
  have loop := progressive_loop_ranked p n roots heap small heapBound rank state code valid budget
  rw [run] at loop
  obtain ⟨nextRank,rankedNext,_,_⟩ := loop.2.2.2 rfl
  obtain ⟨_,_,_,hh,off,size,k,_,_,hk,counters,_⟩ := rankedNext
  exact ⟨hh,k,hk,by obtain ⟨envelope,_,steps⟩ := counters; omega⟩

#print axioms runBounded_progressive_loop
#print axioms progressive_initial_rank
#print axioms progressive_loop_normal_k_bound
#print axioms eval_progressive_condition
#print axioms progressive_loop_ranked
end InitECandidate.Runtime
