import InitECandidate.Runtime.RollbackWorldIterationAllPlansBoundedNoBreak
import InitECandidate.Runtime.RollbackWorldIterationRegisteredValuesIn
import InitECandidate.Runtime.StateRestoreRankedExitsInvariant
import InitECandidate.Runtime.PanEvaluationDomain
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual rollback loop retains watched table values and saved journal values on normal completion, and has a finite bound including allocation-failure exits. -/
theorem RollbackWorld.loop_bounded_registered_values_in {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (budget : 2 ^ 94 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while stateRestoreCondition stateRestoreLoopBody) = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 94 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ n : BitVec 64, RollbackWorld widths tables journal snapshot n post ∧
        RollbackPhysicalSeparated widths tables post ∧ n.toNat ≤ snapshot.toNat ∧
        (∀ address : BitVec 64, address.toNat < 33806089496 → post.memaddrs address) ∧
        (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal n.toNat watched targets post) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ n : BitVec 64,
    RollbackWorld widths tables journal snapshot n current ∧ RollbackPhysicalSeparated widths tables current ∧
    (∀ address : BitVec 64, address.toNat < 33806089496 → current.memaddrs address) ∧
    (∀ other ∈ watched, HashTableValuesIn other targets current) ∧ JournalSavedValuesIn journal n.toNat watched targets current
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address)) stateRestoreCondition =
      some (.val (.word (if stateRestoreRank current = 0 then 0 else 1))) := by
    rintro current ⟨n,valid,_,_⟩
    exact eval_stateRestore_guard_rank current n snapshot valid.counter valid.snapshotLocal
  have entry : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨n,valid,apart,domain,valuesIn,savedIn⟩
    exact ⟨n,valid.dec_clock,apart.after_read (after := decClockHOLFinite current) rfl rfl rfl rfl rfl,domain,(fun other belongs => (valuesIn other belongs).after_read rfl rfl rfl),
      savedIn.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩
  have step : ∀ current, invariant current → 0 < stateRestoreRank current → 2 ^ 74 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 2 ^ 74 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current stateRestoreLoopBody = (none,post) ∧ invariant post ∧ stateRestoreRank post < stateRestoreRank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current stateRestoreLoopBody = (some result,post))) := by
    rintro current ⟨n,valid,apart,domain,valuesIn,savedIn⟩ active ticks
    obtain ⟨result,post,run,cost,remaining,outcome⟩ := valid.iteration_all_plans_bounded_no_break apart active (by omega) domain
    refine ⟨post,(by omega),remaining,?_⟩
    rcases outcome with success | failure
    · obtain ⟨resultNone,postWorld,postApart,decrease⟩ := success
      subst result
      have postDomain : post.memaddrs = current.memaddrs := by
        have preserved := evaluateHOLFiniteState_memaddrs current stateRestoreLoopBody
        rw [run] at preserved
        exact preserved
      have membership := valid.iteration_registered_values_in apart active ticks domain watched targets watchedSubset valuesIn savedIn (by rw [run])
      rw [run] at membership
      exact Or.inl ⟨run,⟨n - 1,postWorld,postApart,(by rw [postDomain]; exact domain),membership.1,membership.2⟩,decrease⟩
    · obtain ⟨nonempty,noTimeout,noContinue,noBreak,noReturn⟩ := failure
      cases result with
      | none => exact False.elim (nonempty rfl)
      | some result => exact Or.inr ⟨result,by simpa using noContinue,by simpa using noTimeout,by simpa using noBreak,(by intro value equal; exact noReturn value (congrArg some equal)),run⟩
  have rankBound : stateRestoreRank state ≤ 524288 := by
    rw [stateRestoreRank_of_bindings state count snapshot world.counter world.snapshotLocal]
    have capacity := world.capacity
    omega
  have total : stateRestoreRank state * (2 ^ 74 + 1) ≤ 2 ^ 94 := by
    have scaled := Nat.mul_le_mul_right (2 ^ 74 + 1) rankBound
    norm_num at scaled ⊢
    omega
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_stateRestore_ranked_exits_invariant invariant stateRestoreRank (2 ^ 74)
    guard entry stateRestoreRank_dec_clock step state ⟨count,world,separated,heapDomain,registered,saved⟩ (by omega)
  refine ⟨result,post,run,by omega,remaining,noTimeout,?_,noReturn⟩
  intro normal
  obtain ⟨⟨n,valid,apart,domain,valuesIn,savedIn⟩,zero⟩ := completed normal
  have rank := stateRestoreRank_of_bindings post n snapshot valid.counter valid.snapshotLocal
  exact ⟨n,valid,apart,by omega,domain,valuesIn,savedIn⟩

#print axioms RollbackWorld.loop_bounded_registered_values_in
end InitECandidate.Runtime
