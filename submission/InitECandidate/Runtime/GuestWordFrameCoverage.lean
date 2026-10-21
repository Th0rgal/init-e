import InitECandidate.Runtime.GuestWordFrameBounds
import InitECandidate.Runtime.WordCodeFrameBounds
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Every actual source function has a declared frame; a missing lookup
cannot silently use the compiler relation's unconstrained default. -/
theorem guest_word_frames_cover :
    InitECandidate.Proofs.BackendStages.Native.programs0.all (fun entry =>
      (sptLookup entry.1 InitECandidate.Proofs.BackendStages.Native.wordConfig.stackFrameSize).isSome) = true := by
  decide_cbv

theorem guest_word_frame_of_mem (entry : Nat × Nat × WordLangProgHOL (BitVec 64))
    (member : entry ∈ InitECandidate.Proofs.BackendStages.Native.programs0) :
    ∃ frame, sptLookup entry.1 InitECandidate.Proofs.BackendStages.Native.wordConfig.stackFrameSize = some frame ∧ frame ≤ 92 := by
  have covered := List.all_eq_true.mp guest_word_frames_cover entry member
  cases found : sptLookup entry.1 InitECandidate.Proofs.BackendStages.Native.wordConfig.stackFrameSize with
  | none => simp [found] at covered
  | some frame => exact ⟨frame, rfl, guest_word_frame_lookup_bound entry.1 frame found⟩

/-- Eligibility for the actual pre-Word-to-Stack source code map. -/
theorem guest_word_code_frames_bounded :
    CodeFramesBounded
      (sptFromAList (InitECandidate.Proofs.BackendStages.Native.programs0.map
        (fun entry => (entry.1, entry.2))))
      InitECandidate.Proofs.BackendStages.Native.wordConfig.stackFrameSize 92 := by
  intro key body found
  rw [sptLookup_sptFromAList] at found
  have member := sptAListLookup_mem key _ body found
  obtain ⟨entry, member, entryEq⟩ := List.mem_map.mp member
  have keyEq : entry.1 = key := congrArg Prod.fst entryEq
  have bounded := guest_word_frame_of_mem entry member
  simpa only [keyEq] using bounded

#print axioms guest_word_code_frames_bounded

#print axioms guest_word_frames_cover
#print axioms guest_word_frame_of_mem
end InitECandidate.Runtime.WordToStack
