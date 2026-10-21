import InitECandidate.Proofs.BackendStages.Native
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000

/-- These are the compiler's original Word-to-Stack frame sizes, rather
than frame operations observed after later optimizations. -/
theorem guest_word_frames_bounded :
    InitECandidate.Proofs.BackendStages.Native.frames0.all (fun frame => decide (frame ≤ 92)) = true := by
  decide_cbv

private theorem lookupNat_bound (entries : List (Nat × Nat)) (limit key value : Nat)
    (checked : entries.all (fun entry => decide (entry.2 ≤ limit)) = true)
    (found : sptLookup key (sptFromAList entries) = some value) : value ≤ limit := by
  rw [sptLookup_sptFromAList] at found
  induction entries with
  | nil => simp [sptAListLookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨name, frame⟩
    simp only [List.all_cons, Bool.and_eq_true] at checked
    simp only [sptAListLookup] at found
    split at found
    · obtain rfl := Option.some.inj found
      exact of_decide_eq_true checked.1
    · exact ih checked.2 found

/-- Every successful lookup in the pinned source stack-size map is small.
Association-list duplicates require no uniqueness assumption. -/
theorem guest_word_frame_lookup_bound (key frame : Nat)
    (found : sptLookup key InitECandidate.Proofs.BackendStages.Native.wordConfig.stackFrameSize = some frame) :
    frame ≤ 92 := by
  apply lookupNat_bound _ 92 key frame ?_ found
  apply List.all_eq_true.mpr
  intro entry member
  obtain ⟨pair, zipMember, pairEq⟩ := List.mem_map.mp member
  subst entry
  have inFrames := (List.of_mem_zip zipMember).2
  exact List.all_eq_true.mp guest_word_frames_bounded pair.2 inFrames

#print axioms guest_word_frames_bounded
#print axioms guest_word_frame_lookup_bound
end InitECandidate.Runtime.WordToStack
