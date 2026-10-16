import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
namespace InitECandidate.Runtime.LabFilter
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabFilter Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.LabFilter.Proofs

/-- A terminating unfiltered execution supplies a filtered execution at the same
initial clock, with exactly the same outcome and FFI state. -/
theorem terminating_same_clock {width : Nat} [NeZero width] {C F : Type}
    (filtered original : State width C F) (post : State width C F) (outcome : HolOutcome)
    (related : Proofs.stateRel filtered original)
    (run : evaluate original = (.halt outcome, post)) :
    ∃ final, evaluate filtered = (.halt outcome, final) ∧ final.ffi = post.ffi := by
  obtain ⟨extra, next, evaluated, ffi⟩ := Proofs.filterCorrect filtered original
    (evaluate filtered).1 (evaluate filtered).2 ⟨rfl, related, related.2⟩
  have extended := evaluateAddClock original (.halt outcome) post extra ⟨run, by simp⟩
  have clockEq : filtered.clock = original.clock := by
    obtain ⟨⟨comp, eq, compiler⟩, notFailed⟩ := related
    rw [eq]
  rw [clockEq, extended] at evaluated
  have result := (Prod.mk.inj evaluated).1.symm
  have nextEq := (Prod.mk.inj evaluated).2
  refine ⟨(evaluate filtered).2, Prod.ext result rfl, ?_⟩
  rw [ffi, ← nextEq]

/-- At the compiler's entry PC, filtering introduces no additional fuel cost. -/
theorem entry_same_clock {width : Nat} [NeZero width] {C F : Type}
    (original : State width C F) (post : State width C F) (outcome : HolOutcome)
    (sourceCompile : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (pc : original.pc = 0) (notFailed : original.failed = false)
    (compiler : original.compile = fun conf program => sourceCompile conf (filterSkip program))
    (run : evaluate original = (.halt outcome, post)) :
    ∃ final, evaluate {original with
      code := filterSkip original.code
      compileOracle := fun n => ((original.compileOracle n).1, filterSkip (original.compileOracle n).2)
      compile := sourceCompile} = (.halt outcome, final) ∧ final.ffi = post.ffi := by
  apply terminating_same_clock _ original post outcome _ run
  refine ⟨⟨sourceCompile, ?_, compiler⟩, notFailed⟩
  have adjusted : adjustPc original.pc original.code = original.pc := by
    rw [pc, adjustPc.eq_def]
    simp
  simp only [adjusted]

#print axioms terminating_same_clock
#print axioms entry_same_clock
end InitECandidate.Runtime.LabFilter
