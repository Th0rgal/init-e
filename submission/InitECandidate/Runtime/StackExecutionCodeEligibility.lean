import InitECandidate.Runtime.StackExecutionEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- A structural artifact certificate discharges eligibility for every
actual installed lookup, including duplicated association-list keys. -/
theorem executionCodeSupported_fromAList (entries : List (Nat × HolProg 64))
    (checked : entries.all (fun entry => executionSupported entry.2) = true) :
    ExecutionCodeSupported (sptFromAList entries) := by
  intro key prog found
  rw [sptLookup_sptFromAList] at found
  induction entries with
  | nil => simp [sptAListLookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨name, body⟩
    simp only [List.all_cons, Bool.and_eq_true] at checked
    simp only [sptAListLookup] at found
    split at found
    · have eq := Option.some.inj found
      subst prog
      exact checked.1
    · exact ih checked.2 found

#print axioms executionCodeSupported_fromAList
end InitECandidate.Runtime.StackToLab
