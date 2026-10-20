import InitECandidate.Runtime.ComputeJumpdestsSource
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- The real constructor suffix after scratch_alloc has no global writes,
including exceptional/timeout outcomes of its actual memzero call. -/
theorem compute_jumpdests_suffix_globals_frame : OriginalGlobalsFrame (computeJumpdestsAt 1) := by
 rw [source_compute_jumpdests_zero]
 exact originalGlobalsFrame_sequence _ _ (memzero_call_globals_frame _)
  (originalGlobalsFrame_leaf _ (by intro watched;rfl))
#print axioms compute_jumpdests_suffix_globals_frame
end InitECandidate.Runtime
