import InitECandidate.Runtime.RollbackWorldIterationAllPlansBoundedNoBreak
import InitECandidate.Runtime.StateRestoreRankedExitsInvariant
import InitECandidate.Runtime.PanEvaluationDomain
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete actual rollback loop has a finite clock bound and cannot time
out from a live separated world, for every allocation plan including failure. -/
theorem RollbackWorld.loop_bounded_success_world {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (budget : 2 ^ 92 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 92 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ n : BitVec 64, RollbackWorld widths tables journal snapshot n post ∧
        RollbackPhysicalSeparated widths tables post ∧ n.toNat ≤ snapshot.toNat ∧
        (∀ address : BitVec 64, address.toNat < 33806089496 → post.memaddrs address)) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ n : BitVec 64,
    RollbackWorld widths tables journal snapshot n current ∧ RollbackPhysicalSeparated widths tables current ∧
    (∀ address : BitVec 64, address.toNat < 33806089496 → current.memaddrs address)
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address)) stateRestoreCondition =
      some (.val (.word (if stateRestoreRank current = 0 then 0 else 1))) := by
    rintro current ⟨n,valid,_,_⟩
    exact eval_stateRestore_guard_rank current n snapshot valid.counter valid.snapshotLocal
  have entry : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨n,valid,apart,domain⟩
    exact ⟨n,valid.dec_clock,apart.after_read (after := decClockHOLFinite current) rfl rfl rfl rfl rfl,domain⟩
  have step : ∀ current, invariant current → 0 < stateRestoreRank current → 2 ^ 72 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current stateRestoreLoopBody = (none,post) ∧ invariant post ∧ stateRestoreRank post < stateRestoreRank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current stateRestoreLoopBody = (some result,post))) := by
    rintro current ⟨n,valid,apart,domain⟩ active ticks
    obtain ⟨result,post,run,cost,remaining,outcome⟩ := valid.iteration_all_plans_bounded_no_break apart active ticks domain
    refine ⟨post,cost,remaining,?_⟩
    rcases outcome with success | failure
    · obtain ⟨resultNone,postWorld,postApart,decrease⟩ := success
      subst result
      have postDomain : post.memaddrs = current.memaddrs := by
        have preserved := evaluateHOLFiniteState_memaddrs current stateRestoreLoopBody
        rw [run] at preserved
        exact preserved
      exact Or.inl ⟨run,⟨n - 1,postWorld,postApart,by rw [postDomain]; exact domain⟩,decrease⟩
    · obtain ⟨nonempty,noTimeout,noContinue,noBreak,noReturn⟩ := failure
      cases result with
      | none => exact False.elim (nonempty rfl)
      | some result => exact Or.inr ⟨result,by simpa using noContinue,by simpa using noTimeout,by simpa using noBreak,(by intro value equal; exact noReturn value (congrArg some equal)),run⟩
  have rankBound : stateRestoreRank state ≤ 524288 := by
    rw [stateRestoreRank_of_bindings state count snapshot world.counter world.snapshotLocal]
    have capacity := world.capacity
    omega
  have total : stateRestoreRank state * (2 ^ 72 + 1) ≤ 2 ^ 92 := by
    have scaled := Nat.mul_le_mul_right (2 ^ 72 + 1) rankBound
    norm_num at scaled ⊢
    omega
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_stateRestore_ranked_exits_invariant invariant stateRestoreRank (2 ^ 72)
    guard entry stateRestoreRank_dec_clock step state ⟨count,world,separated,heapDomain⟩ (by omega)
  refine ⟨result,post,run,by omega,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨⟨n,valid,apart,domain⟩,zero⟩ := completed normal
  have rank := stateRestoreRank_of_bindings post n snapshot valid.counter valid.snapshotLocal
  exact ⟨n,valid,apart,by omega,domain⟩

#print axioms RollbackWorld.loop_bounded_success_world
end InitECandidate.Runtime
