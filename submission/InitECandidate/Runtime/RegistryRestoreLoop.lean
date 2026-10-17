import InitECandidate.Runtime.RegistryRestoreIteration
import InitECandidate.Runtime.TransactionRegistryWorldFrame
import InitECandidate.Runtime.StateRestoreRankedExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full rollback loop preserves the complete transaction invariant on
normal completion within the uniform2^92 source-clock budget. -/
theorem TransactionRegistryWorld.restore_loop {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)} {fieldPointer ts journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (budget : 2 ^ 92 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ n : BitVec 64, TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n post ∧
        post.locals.lookup (ofString "snap") = some (.val (.word snapshot)) ∧ n.toNat ≤ snapshot.toNat) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ n : BitVec 64,
    TransactionRegistryWorld widths tables fieldPointer ts journal snapshot n current ∧
      current.locals.lookup (ofString "snap") = some (.val (.word snapshot))
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address)) stateRestoreCondition =
      some (.val (.word (if stateRestoreRank current = 0 then 0 else 1))) := by
    rintro current ⟨n,world,snap⟩
    exact eval_stateRestore_guard_rank current n snapshot world.journalWorld.world.counter snap
  have entry : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨n,world,snap⟩
    exact ⟨n,world.after_read rfl rfl rfl rfl rfl,snap⟩
  have step : ∀ current, invariant current → 0 < stateRestoreRank current → 2 ^ 72 + 1 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + (2 ^ 72 + 1) ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current stateRestoreLoopBody = (none,post) ∧ invariant post ∧ stateRestoreRank post < stateRestoreRank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState current stateRestoreLoopBody = (some result,post))) := by
    rintro current ⟨n,world,snap⟩ active ticks
    obtain ⟨result,post,run,cost,remaining,outcome⟩ := world.restore_iteration snap active ticks
    refine ⟨post,cost,remaining,?_⟩
    rcases outcome with success | failure
    · obtain ⟨normal,postWorld,postSnap,decrease⟩ := success
      subst result
      exact Or.inl ⟨run,⟨n - 1,postWorld,postSnap⟩,decrease⟩
    · obtain ⟨nonempty,noTimeout,noContinue,noBreak,noReturn⟩ := failure
      cases result with
      | none => exact False.elim (nonempty rfl)
      | some result => exact Or.inr ⟨result,by simpa using noContinue,by simpa using noTimeout,by simpa using noBreak,
          (by intro value equal; exact noReturn value (congrArg some equal)),run⟩
  have rankBound : stateRestoreRank state ≤ 524288 := by
    rw [stateRestoreRank_of_bindings state count snapshot valid.journalWorld.world.counter snapshotLocal]
    have capacity := valid.journalWorld.world.capacity
    omega
  have total : stateRestoreRank state * ((2 ^ 72 + 1) + 1) ≤ 2 ^ 92 := by
    have scaled := Nat.mul_le_mul_right ((2 ^ 72 + 1) + 1) rankBound
    norm_num at scaled ⊢
    omega
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ :=
    evaluate_stateRestore_ranked_exits_invariant invariant stateRestoreRank (2 ^ 72 + 1)
      guard entry stateRestoreRank_dec_clock step state ⟨count,valid,snapshotLocal⟩ (by omega)
  refine ⟨result,post,run,by omega,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨⟨n,world,snap⟩,zero⟩ := completed normal
  have rank := stateRestoreRank_of_bindings post n snapshot world.journalWorld.world.counter snap
  exact ⟨n,world,snap,by omega⟩

#print axioms TransactionRegistryWorld.restore_loop
end InitECandidate.Runtime
