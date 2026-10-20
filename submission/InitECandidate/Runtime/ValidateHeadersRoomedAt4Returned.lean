import InitECandidate.Runtime.ValidateHeadersRoomedExitLocals
import InitECandidate.Runtime.ValidateHeadersStoredRootsFinalParent
import InitECandidate.Runtime.ValidateHeadersSecondPhaseFrame
import InitECandidate.Runtime.ReachesReturnedContinuation
/-!
The actual `validateHeadersAt 4` returned contract.

The first loop is entered at index 4 with the roomed invariant; when it completes, the run's own
returned value is the `rStruct` pair of the header-pointer buffer and the hash buffer, and the final
state of that run still carries the parent record selected for the last header together with the
live heap binding.  Nothing about the caller's `h` or a parent selector is assumed: the exit state
comes from the reaches of the loop itself.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- **The At4 returned contract.**  Given the roomed invariant at entry and fuel for the actual
first loop, the value the run returns is the `rStruct` pair naming `hs` and `hashes`, and the run's
final state holds the live heap pointer, the parent cell `hs[count-1]`, its state root word, its
domain, the extent below the live heap and the fixed floor below the header. -/
theorem validate_headers_roomed_at4_returned {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (valid : ValidateHeadersStoredRootsRoomedInvariant e s rank)
    (countNonzero : e.count ≠ 0)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (validateHeadersAt 4) = (some (.returned value),post)) :
    value = .rStruct [.val (.word e.hs),.val (.word e.hashes)] ∧
      ∃ heap header word : BitVec 64,
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
        post.memory (e.hs + (e.count - 1) * 8) = .word header ∧
        post.memory (header + 32#64) = .word word ∧ post.memaddrs (header + 32#64) ∧
        header.toNat + 248 ≤ heap.toNat ∧
        e.hashes.toNat + e.count.toNat * 32 + 32 ≤ header.toNat := by
  have reached := validate_headers_stored_roots_roomed_loop_reaches (F := F) e s rank code hsAbove
    bufferBeforeHashes valid budget
  obtain ⟨stop,accepted,_,_,agreement,tailValue⟩ :=
    reaches_returned_continuation (F := F) s (validateHeadersAt 4) (validateHeadersAt 5) _ _ value
      reached (congrArg Prod.fst run)
  generalize hstep : evaluateHOLFiniteState stop (validateHeadersAt 5) = step at tailValue agreement
  obtain ⟨result,middle⟩ := step
  have resultEq : result = some (.returned value) := tailValue
  subst resultEq
  rw [run] at agreement
  obtain ⟨_,_,memoryEq,globalsEq,addrsEq⟩ := agreement
  have locals := validate_headers_roomed_exit_locals (F := F) e stop accepted.1
  have shape := evaluate_validate_headers_second_phase_returned (F := F) stop e.hs e.hashes value
    middle (accepted.2.trans code) locals.1 locals.2 hstep
  obtain ⟨pair,frameMemory,frameGlobals,frameDomain,_,_⟩ := shape
  obtain ⟨heap,header,word,heapGlobal,cell,rooted,domain,extent,above⟩ :=
    validate_headers_stored_roots_parent_exhausted (F := F) e stop accepted.1.1 countNonzero
  refine ⟨pair,heap,header,word,?_,?_,?_,?_,?_,?_⟩
  · rw [globalsEq,frameGlobals]
    exact heapGlobal
  · rw [memoryEq,frameMemory]
    exact cell
  · rw [memoryEq,frameMemory]
    exact rooted
  · rw [addrsEq,frameDomain]
    exact domain
  · exact extent
  · exact above

#print axioms validate_headers_roomed_at4_returned
end InitECandidate.Runtime
