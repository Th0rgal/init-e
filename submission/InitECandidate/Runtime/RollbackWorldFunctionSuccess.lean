import InitECandidate.Runtime.RollbackWorldLoopSuccess
import InitECandidate.Runtime.RollbackWorldLogicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful completion of the full original restore body retains a separated
world at or below the requested snapshot. Exceptional allocation exits cannot
masquerade as the body's final successful return. -/
theorem RollbackWorld.function_bounded_success_world {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 2 ^ 92 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_restore) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ n : BitVec 64,
        RollbackWorld widths tables journal snapshot n (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
        RollbackPhysicalSeparated widths tables post ∧ n.toNat ≤ snapshot.toNat) := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := world.loop_bounded_success_world separated heapDomain budget
  rw [source_stateRestore_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    obtain ⟨n,valid,apart,done,_⟩ := completed rfl
    have returned : evaluateHOLFiniteState post (.return (.const 0)) =
        (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    dsimp only
    rw [returned]
    refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
    intro value success
    exact ⟨n,valid.after_logical_frame rfl rfl rfl rfl rfl,apart.after_read rfl rfl rfl rfl rfl,done⟩
  | some result =>
    refine ⟨some result,post,rfl,cost,remaining,noTimeout,?_⟩
    intro value success
    exact False.elim (noReturn value success)

#print axioms RollbackWorld.function_bounded_success_world
end InitECandidate.Runtime
