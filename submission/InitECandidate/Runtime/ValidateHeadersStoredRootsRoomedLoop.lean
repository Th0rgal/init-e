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

#print axioms validate_headers_stored_roots_roomed_dec_clock
end InitECandidate.Runtime
