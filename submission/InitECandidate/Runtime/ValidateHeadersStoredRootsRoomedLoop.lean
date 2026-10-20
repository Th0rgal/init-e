import InitECandidate.Runtime.ValidateHeadersStoredRootsRoomedStep
import InitECandidate.Runtime.ValidateHeadersFirstPointerLoop
/-!
The conditional ranked first loop for the roomed stored-roots invariant.

All outcomes are bounded by the existing runtime body bound on the pointer-invariant projection,
which carries no room premise: low-room iterations that fail are still covered.  Only the normal
outcome uses the roomed preservation step, and the clock decrement keeps the invariant because it
leaves the heap and the data unchanged.  The final parent selection and the canonical initial
margin are not part of this theorem.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The clock decrement leaves the roomed invariant intact: no data, heap or memory changes. -/
theorem validate_headers_stored_roots_roomed_dec_clock {F : Type}
    (e : ValidateHeadersFirstEnvironment) (s : PanSemStateFiniteExact 64 F) (rank : Nat)
    (valid : ValidateHeadersStoredRootsRoomedInvariant e s rank) :
    ValidateHeadersStoredRootsRoomedInvariant e (decClockHOLFinite s) rank := by
  obtain ⟨stored,room⟩ := valid
  obtain ⟨pointer,⟨index,heap,atIndex,heapGlobal,floorBelow,roots⟩⟩ := stored
  obtain ⟨ticked,⟨prefixIndex,atPrefixIndex,initialized⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩ :=
    pointer
  have tickedPointer : ValidateHeadersFirstPointerInvariant e (decClockHOLFinite s) rank :=
    ⟨validate_headers_first_invariant_dec_clock e s rank ticked,⟨prefixIndex,atPrefixIndex,
        HeaderPointerPrefix.after_frame s (decClockHOLFinite s) e.hs prefixIndex.toNat initialized
          rfl (fun slot _ => rfl)⟩,⟨initialHeap,initialBinding,bufferBefore⟩⟩
  refine ⟨⟨tickedPointer,⟨index,heap,?_,?_,floorBelow,?_⟩⟩,?_⟩
  · simpa [decClockHOLFinite] using atIndex
  · simpa [decClockHOLFinite] using heapGlobal
  · exact roots
  · intro heap' binding
    exact room heap' binding


/-- **The conditional ranked first loop.** Every outcome is bounded by the runtime body bound on
the pointer-invariant projection, which needs no room; only normal iterations use the roomed
preservation step; continue and break cannot occur.  The rank strictly decreases and the roomed
invariant is preserved, so the ranked outcome follows with the invariant as its predicate. -/
theorem validate_headers_stored_roots_roomed_loop_ranked (e : ValidateHeadersFirstEnvironment)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat) :
    ∀ rank, ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      ValidateHeadersStoredRootsRoomedInvariant e s rank →
      rank * (validateHeadersFirstIterationCost e.inputLimit + 1) ≤ s.clock →
      RankedOutcome s validateHeadersFirstCondition
        (rank * (validateHeadersFirstIterationCost e.inputLimit + 1))
        (ValidateHeadersStoredRootsRoomedInvariant e) False
        (evaluateHOLFiniteState s (.while validateHeadersFirstCondition validateHeadersFirstBody)) := by
  apply rankedWhile_run validateHeadersFirstCondition validateHeadersFirstBody
    (validateHeadersFirstIterationCost e.inputLimit) (ValidateHeadersStoredRootsRoomedInvariant e) False
  · intro F s valid w condition
    exact validate_headers_first_invariant_exit e s valid.1.1.1 w condition
  · intro F s n w code valid condition nonzero budget
    have ticked := validate_headers_first_invariant_dec_clock e s (n+1) valid.1.1.1
    have tickedRoom := validate_headers_stored_roots_roomed_dec_clock e s (n+1) valid
    have tickCondition : evalHOLFinite (decClockHOLFinite s)
        (h := fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
        validateHeadersFirstCondition = some (.val (.word w)) := by
      rw [evalHOLFinite_eq_toExact] at condition ⊢
      simpa [validateHeadersFirstCondition,evalHOLExact,decClockHOLFinite] using condition
    have bodyBudget : validateHeadersFirstIterationCost e.inputLimit ≤ (decClockHOLFinite s).clock := by
      change validateHeadersFirstIterationCost e.inputLimit ≤ s.clock - 1
      omega
    have bounded := runBounded_validate_headers_first_invariant_body e (decClockHOLFinite s) (n+1)
      ticked code w tickCondition nonzero bodyBudget
    have controls := validate_headers_first_body_no_loop_control (decClockHOLFinite s)
    refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_,?_⟩
    · intro flow
      have normal := flow.resolve_right controls.1
      have run : evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody =
          (none,(evaluateHOLFiniteState (decClockHOLFinite s) validateHeadersFirstBody).2) :=
        Prod.ext normal rfl
      obtain ⟨m,smaller,nextInvariant⟩ := validate_headers_stored_roots_roomed_step e
        (decClockHOLFinite s) _ (n+1) hsAbove bufferBeforeHashes tickedRoom code w tickCondition
        nonzero bodyBudget run
      exact ⟨m,by omega,nextInvariant,
        (evaluateHOLFiniteState_metadata (decClockHOLFinite s) validateHeadersFirstBody).1⟩
    · intro broken
      exact (controls.2 broken).elim

#print axioms validate_headers_stored_roots_roomed_loop_ranked

#print axioms validate_headers_stored_roots_roomed_dec_clock
end InitECandidate.Runtime
