import InitECandidate.Runtime.StackRemovalReachableCorrect
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- First-match code lookup preserves the two independent syntactic
certificates, including when the input association list has duplicate keys. -/
theorem avoidingRemovalCode_fromAList (forbidden : Nat) (entries : List (Nat × HolProg 64))
    (eligible : entries.all (fun entry => decide (entry.1 = forbidden) || removalSupported entry.2) = true)
    (closed : entries.all (fun entry => directCallsAvoid forbidden entry.2) = true) :
    AvoidingRemovalCode forbidden (sptFromAList entries) := by
  intro key p found allowed
  rw [sptLookup_sptFromAList] at found
  induction entries with
  | nil => simp [sptAListLookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨name, body⟩
    simp only [List.all_cons, Bool.and_eq_true] at eligible closed
    simp only [sptAListLookup] at found
    split at found
    · rename_i same
      obtain rfl := Option.some.inj found
      refine ⟨?_, closed.1⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at eligible
      rcases eligible.1 with excluded | supported
      · exact False.elim (allowed (same.trans excluded))
      · exact supported
    · exact ih eligible.2 closed.2 found

#print axioms avoidingRemovalCode_fromAList
end InitECandidate.Runtime.StackToLab
