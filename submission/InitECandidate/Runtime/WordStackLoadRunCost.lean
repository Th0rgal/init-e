import InitECandidate.Runtime.WordStackSpillCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Spill-prefix composition at its actual post-state. Unlike a uniform
suffix ceiling, this lemma preserves the specific state needed by a branch
or a recursive compiler simulation. -/
theorem wordStackLoad_cost_run {F : Type} (loads : List (Nat × Nat))
    (body : HolProg 64)
    (source loaded : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (small : ∀ entry ∈ loads, entry.2 ≤ 91)
    (run : StackSemEvaluate.evaluate
      (WordToStack.Native.wStackLoadNative loads .skip, source) = (none, loaded)) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (WordToStack.Native.wStackLoadNative loads body) source ≤
      7 * loads.length +
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body loaded := by
  induction loads generalizing source with
  | nil =>
    simp only [WordToStack.Native.wStackLoadNative, StackSemEvaluate.evaluate_skip,
      Prod.mk.injEq, true_and] at run
    subst loaded
    simp only [WordToStack.Native.wStackLoadNative, List.length_nil, Nat.mul_zero,
      Nat.zero_add, Nat.le_refl]
  | cons entry rest ih =>
    rcases entry with ⟨register, offset⟩
    have headSmall : offset ≤ 91 := small (register, offset) (by simp)
    have tailSmall : ∀ entry ∈ rest, entry.2 ≤ 91 := fun entry mem => small entry (by simp [mem])
    rw [WordToStack.Native.wStackLoadNative, StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate] at run
    rcases headRun : StackSemEvaluate.evaluate (.stackLoad register offset, source) with ⟨result, middle⟩
    rw [headRun] at run
    cases result with
    | some output => cases (Prod.mk.inj run).1
    | none =>
      have suffix := ih middle tailSmall run
      rw [WordToStack.Native.wStackLoadNative, stackExecutionCost_seq]
      simp only [show removalLocalPrice 6 riscvConfig.addrOffset
          (.seq (.stackLoad register offset) (WordToStack.Native.wStackLoadNative rest body)) = 0 from rfl,
        Nat.zero_add, headRun]
      have localCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (.stackLoad register offset) source = 7 := by
        simp only [stackExecutionCost, guest_spill_load_price register offset headSmall]
      rw [localCost]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

#print axioms wordStackLoad_cost_run
end InitECandidate.Runtime.StackToLab
