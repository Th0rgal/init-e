import InitECandidate.Runtime.ValidateHeadersFirstAlignedHeapLoop
import InitECandidate.Runtime.ValidateHeadersFirstInvariantWindowStep
import InitECandidate.Runtime.ValidateHeadersFirstLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- The aligned heap invariant plus unchanged older memory, relative to a
fixed entry memory. This covers the stateless record and earlier witnesses. -/
def ValidateHeadersFirstWindowInvariant (e : ValidateHeadersFirstEnvironment) (memory : BitVec 64 → HolWordLab 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ValidateHeadersFirstAlignedHeapInvariant e e.hs s rank ∧
    ∀ address : BitVec 64, e.ceiling ≤ address.toNat → address.toNat < e.hs.toNat → s.memory address = memory address

/-- The actual ranked loop retains monotonic heap growth as well as the
original witness/workspace invariant on normal exit, with the same budget. -/
theorem validate_headers_first_window_loop_ranked (e : ValidateHeadersFirstEnvironment) (memory : BitVec 64 → HolWordLab 64) :
    ∀ rank, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersFirstWindowInvariant e memory s rank → rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ s.clock →
      RankedOutcome s validateHeadersFirstCondition (rank * (validateHeadersFirstIterationCost e.inputLimit + 1))
        (ValidateHeadersFirstWindowInvariant e memory) False
        (evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody)) := by
  apply rankedWhile_run validateHeadersFirstCondition validateHeadersFirstBody (validateHeadersFirstIterationCost e.inputLimit)
    (ValidateHeadersFirstWindowInvariant e memory) False
  · intro F s valid w condition
    exact validate_headers_first_invariant_exit e s valid.1.1 w condition
  · intro F s n w code valid condition nonzero budget
    obtain ⟨alignedInv,window⟩ := valid
    obtain ⟨invariant,heap,heapBinding,lowerBound,aligned⟩ := alignedInv
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
      have frame := validate_headers_first_invariant_window_step e (decClockHOLFinite s) _ (n+1) heap
        ticked code w tickCondition nonzero bodyBudget heapBinding lowerBound run
      exact ⟨m,by omega,⟨⟨nextInv,nextHeap,nextBinding,le_trans lowerBound growth,nextAligned⟩,
        fun address lo hi => (frame address lo hi).trans (window address lo hi)⟩,
        (evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersFirstBody).1⟩
    · intro broken
      exact (controls.2 broken).elim

#print axioms validate_headers_first_window_loop_ranked
end InitECandidate.Runtime
