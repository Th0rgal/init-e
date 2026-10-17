import InitECandidate.Runtime.StateRestoreRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original rollback function bound, conditional on the concrete
world invariant and successful record-step preservation. The capacity is the
524288-record journal allocated by the frozen state_init source. -/
theorem evaluate_stateRestore_function_bounded {F : Type}
    (invariant : PanSemStateFiniteExact 64 F → Prop)
    (bindings : ∀ state, invariant state → ∃ count snapshot : BitVec 64,
      state.globals.lookup (ofString "journal_n") = some (.val (.word count)) ∧
      state.locals.lookup (ofString "snap") = some (.val (.word snapshot)) ∧ count.toNat ≤ 524288)
    (entryInvariant : ∀ state, invariant state → invariant (decClockHOLFinite state))
    (step : ∀ state, invariant state → 0 < stateRestoreRank state → 2 ^ 72 ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state stateRestoreLoopBody = (none,post) ∧ invariant post ∧
        stateRestoreRank post < stateRestoreRank state ∧ state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock)
    (state : PanSemStateFiniteExact 64 F) (valid : invariant state) (budget : 2 ^ 92 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_restore) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) ∧
      invariant post ∧ stateRestoreRank post = 0 ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock := by
  have rankBound : stateRestoreRank state ≤ 524288 := by
    obtain ⟨count,snapshot,counter,snap,capacity⟩ := bindings state valid
    rw [stateRestoreRank_of_bindings state count snapshot counter snap]
    omega
  have scaled := Nat.mul_le_mul_right (2 ^ 72 + 1) rankBound
  have numeric : stateRestoreRank state * (2 ^ 72 + 1) ≤ 2 ^ 92 := by
    norm_num at scaled ⊢
    omega
  have guard : ∀ current, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) stateRestoreCondition =
        some (.val (.word (if stateRestoreRank current = 0 then 0 else 1))) := by
    intro current currentValid
    obtain ⟨count,snapshot,counter,snap,_⟩ := bindings current currentValid
    exact eval_stateRestore_guard_rank current count snapshot counter snap
  obtain ⟨post,loop,postValid,done,cost,remaining⟩ := evaluate_stateRestore_ranked invariant stateRestoreRank (2 ^ 72)
    guard entryInvariant stateRestoreRank_dec_clock step state valid (by omega)
  refine ⟨post,?_,postValid,done,by omega,remaining⟩
  rw [source_stateRestore_body,evaluateHOLFiniteState_seq_line780,loop]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms evaluate_stateRestore_function_bounded
end InitECandidate.Runtime
