import InitECandidate.Runtime.StackWorkCeiling
import InitECandidate.Runtime.StackEntryBudget
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps

theorem workCeiling_mono (limit oldFuel newFuel oldNodes newNodes : Nat)
    (clock : oldFuel ≤ newFuel) (nodes : oldNodes ≤ newNodes) :
    workCeiling limit oldFuel oldNodes ≤ workCeiling limit newFuel newNodes := by
  have scaled := Nat.mul_le_mul_right (limit + 1) clock
  apply Nat.pow_le_pow_right (by decide)
  unfold workRank
  omega

/-- Entry and the possible final halt procedure each have the uniform code-size
ceiling at the original fuel. No termination or final-halt assumption is needed. -/
theorem entryWork_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit start : Nat) (s : StackSemStateFiniteExact width C F) (bounded : CodeSizeState limit s) :
    entryWork start s ≤ 2 * workCeiling limit s.clock limit := by
  rw [entryWork]
  cases found : sptLookup start s.code with
  | none => exact Nat.zero_le _
  | some prog =>
    let entry := decClock s
    let returned := StackSemEvaluate.evaluate (prog, entry)
    have entryClock : entry.clock ≤ s.clock := by simp only [entry, decClock]; omega
    have progSize := bounded.code start prog found
    have first := Nat.le_trans (stackWork_ceiling limit prog entry progSize bounded.decClock)
      (workCeiling_mono limit entry.clock s.clock (sizeOf prog) limit entryClock progSize)
    have returnedBound : CodeSizeState limit returned.2 :=
      CodeSizeState.of_evaluate (p := prog) (s := entry) (result := returned.1) (t := returned.2)
        rfl bounded.decClock
    have returnedClock : returned.2.clock ≤ s.clock :=
      Nat.le_trans (StackSemEvaluateClock.evaluateClock prog entry returned.1 returned.2 rfl) entryClock
    have last : ∀ n haltProg, sptLookup n returned.2.code = some haltProg →
        stackWork haltProg returned.2 ≤ workCeiling limit s.clock limit := by
      intro n haltProg lookup
      have bodySize := returnedBound.code n haltProg lookup
      exact Nat.le_trans (stackWork_ceiling limit haltProg returned.2 bodySize returnedBound)
        (workCeiling_mono limit returned.2.clock s.clock (sizeOf haltProg) limit returnedClock bodySize)
    change stackWork prog entry + (match returned.1 with
      | some (.result (.loc n 0)) => match sptLookup n returned.2.code with
        | none => 0
        | some haltProg => stackWork haltProg returned.2
      | _ => 0) ≤ 2 * workCeiling limit s.clock limit
    split
    · rename_i n resultEq
      split
      · omega
      · rename_i haltProg lookup
        have finalBound := last n haltProg lookup
        omega
    · omega

#print axioms entryWork_ceiling
end InitECandidate.Runtime.StackToLab
