import InitECandidate.Runtime.ValidateHeadersStoredRootsFinalParent
import InitECandidate.Runtime.ValidateHeadersSecondPhaseFrame
/-!
The selected parent survives the actual second phase.

`validateHeadersSecondLoop` is a memory frame: it writes neither memory nor globals.  So the
pointer cell `hs[count-1]` and the parent's state root word, both of which the first loop stored,
are still readable after the second phase has run - which is what the whole-body returned contract
has to carry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The parent record selected at `hs[count-1]` and its state root word survive the second
phase. -/
theorem validate_headers_parent_survives_second_phase {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hs count : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s validateHeadersSecondLoop = (none,post))
    (parent : ∃ header word : BitVec 64,
      s.memory (hs + (count - 1) * 8) = .word header ∧
      s.memory (header + 32#64) = .word word) :
    ∃ header word : BitVec 64,
      post.memory (hs + (count - 1) * 8) = .word header ∧
      post.memory (header + 32#64) = .word word := by
  obtain ⟨header,word,cell,rooted⟩ := parent
  have frameMemory := (validateHeadersSecondLoop_memoryFrame s code).1
  rw [run] at frameMemory
  refine ⟨header,word,?_,?_⟩
  · rw [frameMemory]
    exact cell
  · rw [frameMemory]
    exact rooted

#print axioms validate_headers_parent_survives_second_phase
end InitECandidate.Runtime
