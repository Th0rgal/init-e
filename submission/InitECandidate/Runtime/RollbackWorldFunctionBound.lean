import InitECandidate.Runtime.RollbackWorldLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original complete rollback function body cannot time out within this
uniform budget from the concrete world invariant, including allocation failure. -/
theorem RollbackWorld.function_bounded_no_timeout {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 2 ^ 92 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_restore) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := world.loop_bounded_no_timeout separated heapDomain budget
  rw [source_stateRestore_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have returned : evaluateHOLFiniteState post (.return (.const 0)) =
        (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    dsimp only
    rw [returned]
    exact ⟨_,_,rfl,cost,remaining,by simp⟩
  | some result =>
    exact ⟨some result,post,rfl,cost,remaining,noTimeout⟩

#print axioms RollbackWorld.function_bounded_no_timeout
end InitECandidate.Runtime
