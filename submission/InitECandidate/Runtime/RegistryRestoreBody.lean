import InitECandidate.Runtime.RegistryRestoreLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full frozen restore body preserves the transaction invariant after
its final return clears callee locals. Exceptional loop exits cannot return. -/
theorem TransactionRegistryWorld.restore_body {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (budget : 2 ^ 92 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_restore) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ n : BitVec 64,
        TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n post ∧ n.toNat ≤ snapshot.toNat) := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := valid.restore_loop snapshotLocal budget
  rw [source_stateRestore_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    obtain ⟨n,world,_,done⟩ := completed rfl
    have returned : evaluateHOLFiniteState post (.return (.const 0)) =
        (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    dsimp only
    rw [returned]
    refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
    intro value success
    exact ⟨n,world.after_read rfl rfl rfl rfl rfl,done⟩
  | some result =>
    refine ⟨some result,post,rfl,cost,remaining,noTimeout,?_⟩
    intro value success
    exact False.elim (noReturn value success)

#print axioms TransactionRegistryWorld.restore_body
end InitECandidate.Runtime
