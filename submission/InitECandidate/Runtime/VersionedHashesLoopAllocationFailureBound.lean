import InitECandidate.Runtime.VersionedHashesAllocationFailureControl
import InitECandidate.Runtime.VersionedHashesStepControl
import InitECandidate.Runtime.VersionedHashesLoopRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- With an exhausted initial heap, the complete original loop executes at
most one terminal transaction step. No input or cumulative reserve is assumed. -/
theorem evaluate_versioned_hashes_loop_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 5 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state versionedHashesLoop
    state.clock ≤ evaluated.2.clock + 5 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_versioned_hashes_loop,evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · omega
      · have bounded := evaluate_versioned_hashes_allocation_failure_bounded (decClockHOLFinite state) heap code heapGlobal request
          (by change 4 ≤ state.clock - 1; omega)
        have terminal := versioned_hashes_allocation_failure_control (decClockHOLFinite state) heap code heapGlobal request
        have control := versioned_hashes_step_no_loop_control (decClockHOLFinite state)
        dsimp only
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) versionedHashesStep with
        | mk result post =>
          rw [bodyRun] at bounded terminal control
          dsimp only at bounded terminal control
          have noClamp : ¬(decClockHOLFinite state).clock < post.clock := Nat.not_lt.mpr bounded.2.1
          simp only [fixClockHOLFinite,if_neg noClamp]
          cases result with
          | none => exact False.elim (terminal.1 rfl)
          | some result =>
            cases result <;> simp_all [decClockHOLFinite] <;> omega
    · dsimp only
      exact ⟨by omega,Nat.le_refl _,by simp⟩
  · dsimp only
    exact ⟨by omega,Nat.le_refl _,by simp⟩

#print axioms evaluate_versioned_hashes_loop_allocation_failure_bounded
end InitECandidate.Runtime
