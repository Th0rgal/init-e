import InitECandidate.Runtime.GuestRemovalEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

theorem removalCodeSupported_fromAList (entries : List (Nat × HolProg 64))
    (checked : entries.all (fun entry => removalSupported entry.2) = true) :
    RemovalCodeSupported (sptFromAList entries) := by
  intro key p found
  rw [sptLookup_sptFromAList] at found
  induction entries with
  | nil => simp [sptAListLookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨name, body⟩
    simp only [List.all_cons, Bool.and_eq_true] at checked
    simp only [sptAListLookup] at found
    split at found
    · have eq := Option.some.inj found
      subst p
      exact checked.1
    · exact ih checked.2 found

theorem guest_removal_code_supported : RemovalCodeSupported
    (sptFromAList InitECandidate.Proofs.BackendStages.Alloc.bodies0) :=
  removalCodeSupported_fromAList _ guest_removal_supported

#print axioms guest_removal_code_supported
end InitECandidate.Runtime.StackToLab
