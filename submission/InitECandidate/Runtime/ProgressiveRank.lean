import InitECandidate.Runtime.ProgressiveStepReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ProgressiveRank (p n roots heap : BitVec 64) {F : Type}
    (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  state.locals.lookup (ofString "p") = some (.val (.word p)) ∧
  state.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  state.locals.lookup (ofString "roots") = some (.val (.word roots)) ∧
  state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
  ∃ off size k : BitVec 64,
    state.locals.lookup (ofString "off") = some (.val (.word off)) ∧
    state.locals.lookup (ofString "size") = some (.val (.word size)) ∧
    state.locals.lookup (ofString "k") = some (.val (.word k)) ∧
    ProgressiveCounters n off size k ∧ n.toNat - off.toNat ≤ rank

theorem progressive_rank_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64) (rank : Nat) (small : n.toNat ≤ 134217712)
    (valid : ProgressiveRank p n roots heap state rank)
    (running : ∀ off : BitVec 64, state.locals.lookup (ofString "off") = some (.val (.word off)) → off.toNat < n.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state progressiveStep = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ProgressiveRank p n roots heap post nextRank := by
  obtain ⟨hp,hn,hr,hh,off,size,k,ho,hs,hk,counters,rankBound⟩ := valid
  have next := progressive_step_normal state post p n off size roots k heap hp hn ho hs hr hk hh code run
  have arithmetic := progressive_counters_step n off size k small counters (running off ho)
  refine ⟨n.toNat - (off + size).toNat,by omega,?_,?_,?_,next.1,off + size,size <<< (2 : Nat),k + (1#64),?_,?_,?_,arithmetic.2.2.2.1,le_refl _⟩
  · rw [next.2 _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hp
  · rw [next.2 _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hn
  · rw [next.2 _ (by decide),progressive_update_other_local _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hr
  · rw [next.2 _ (by decide)]; exact (progressive_update_fields state off size k).1
  · rw [next.2 _ (by decide)]; exact (progressive_update_fields state off size k).2.1
  · rw [next.2 _ (by decide)]; exact (progressive_update_fields state off size k).2.2

#print axioms progressive_rank_normal
end InitECandidate.Runtime
