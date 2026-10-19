import InitECandidate.Runtime.ValidateHeadersFirstInvariantAlignedHeapStep
import InitECandidate.Runtime.ValidateHeadersFirstLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- A compatible stronger invariant retains the heap frontier's initial lower
bound through all normal iterations without changing existing contracts. -/
def ValidateHeadersFirstAlignedHeapInvariant (e : ValidateHeadersFirstEnvironment) (lower : BitVec 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ValidateHeadersFirstInvariant e s rank ∧ ∃ heap : BitVec 64,
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧ lower.toNat ≤ heap.toNat ∧ heap.toNat % 8 = 0

/-- The actual ranked loop retains monotonic heap growth as well as the
original witness/workspace invariant on normal exit, with the same budget. -/
theorem validate_headers_first_aligned_heap_loop_ranked (e : ValidateHeadersFirstEnvironment) (lower : BitVec 64) :
    ∀ rank, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersFirstAlignedHeapInvariant e lower s rank → rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ s.clock →
      RankedOutcome s validateHeadersFirstCondition (rank * (validateHeadersFirstIterationCost e.inputLimit + 1))
        (ValidateHeadersFirstAlignedHeapInvariant e lower) False
        (evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody)) := by
  apply rankedWhile_run validateHeadersFirstCondition validateHeadersFirstBody (validateHeadersFirstIterationCost e.inputLimit)
    (ValidateHeadersFirstAlignedHeapInvariant e lower) False
  · intro F s valid w condition
    exact validate_headers_first_invariant_exit e s valid.1 w condition
  · intro F s n w code valid condition nonzero budget
    obtain ⟨invariant,heap,heapBinding,lowerBound,aligned⟩ := valid
    have ticked := validate_headers_first_invariant_dec_clock e s (n+1) invariant
    have tickCondition : evalHOLFinite (decClockHOLFinite s)
        (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a)) validateHeadersFirstCondition = some (.val (.word w)) := by
      rw [evalHOLFinite_eq_toExact] at condition ⊢
      simpa [validateHeadersFirstCondition,evalHOLExact,decClockHOLFinite] using condition
    have bodyBudget : validateHeadersFirstIterationCost e.inputLimit ≤ (decClockHOLFinite s).clock := by
      change validateHeadersFirstIterationCost e.inputLimit ≤ s.clock - 1
      omega
    have bounded := runBounded_validate_headers_first_invariant_body e (decClockHOLFinite s) (n+1) ticked code w tickCondition nonzero bodyBudget
    have controls := validate_headers_first_body_no_loop_control (decClockHOLFinite s)
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      have normal := flow.resolve_right controls.1
      have run : evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody =
          (none,(evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody).2) := Prod.ext normal rfl
      obtain ⟨m,smaller,nextInv,nextHeap,nextBinding,growth,nextAligned⟩ := validate_headers_first_invariant_aligned_heap_step e
        (decClockHOLFinite s) _ (n+1) heap ticked code w tickCondition nonzero bodyBudget heapBinding run
      exact ⟨m,by omega,⟨nextInv,nextHeap,nextBinding,le_trans lowerBound growth,nextAligned⟩,
        (evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersFirstBody).1⟩
    · intro broken
      exact (controls.2 broken).elim

#print axioms validate_headers_first_aligned_heap_loop_ranked
end InitECandidate.Runtime
