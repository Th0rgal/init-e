import InitECandidate.Runtime.StackExecutionCostClockRaw
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Cost stability at one state, used by the clock-first induction. -/
def CostClockStableAt {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ post result, StackSemEvaluate.evaluate (p, source) = (result, post) → result ≠ some .timeOut →
    ∀ extra, stackExecutionCost (fun p _ => price p) p {source with clock := source.clock + extra} =
      stackExecutionCost (fun p _ => price p) p source

theorem stackCost_addClock_return {F : Type} (price : HolProg 64 → Nat)
    (rp : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      child.clock < source.clock → CostClockStableAt price q child) :
    CostClockStableAt price (.call (some (rp, link, l1, l2)) dest handler) source := by
  intro post result run notTimeout extra
  rw [StackSemEvaluate.evaluate_call] at run
  dsimp only at run
  rw [stackExecutionCost.eq_7 (fun p _ => price p) {source with clock := source.clock + extra} rp link l1 l2 dest handler,
    stackExecutionCost.eq_7 (fun p _ => price p) source rp link l1 l2 dest handler]
  cases found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [found]
    split <;> split <;> rfl
  | some body =>
    simp only [found] at run
    have positive : source.clock ≠ 0 := by
      intro zero
      rw [if_pos zero] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    have shiftedPositive : source.clock + extra ≠ 0 := by omega
    simp only [positive, shiftedPositive, ↓reduceIte, found]
    rw [if_neg positive, StackSemEvaluateClock.fixClockEvaluate] at run
    let entry := StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)
    have entryLt : entry.clock < source.clock := by
      change source.clock - 1 < source.clock
      omega
    have entryShift : StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2)
        {source with clock := source.clock + extra}) = {entry with clock := entry.clock + extra} := by
      simp only [entry, StackSemStateOps.decClock, StackSemStateOps.setVar]
      congr 1
      omega
    rw [entryShift]
    rcases bodyRun : StackSemEvaluate.evaluate (body, entry) with ⟨bodyResult, middle⟩
    rw [bodyRun] at run
    have bodyNotTimeout : bodyResult ≠ some .timeOut := by
      intro eq
      rw [eq] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    have bodyCost := ih body entry entryLt middle bodyResult bodyRun bodyNotTimeout extra
    have shifted := StackProps.evaluateAddClock extra body entry bodyResult middle ⟨bodyRun, bodyNotTimeout⟩
    simp only [StackSemEvaluateClock.fixClockEvaluate]
    rw [bodyCost, shifted]
    have clockLe := StackSemEvaluateClock.evaluateClock body entry bodyResult middle bodyRun
    have fixed : StackSemControl.fixClock entry (bodyResult, middle) = (bodyResult, middle) := by
      simp only [StackSemControl.fixClock, Nat.min_eq_right clockLe]
    rw [fixed]
    dsimp only
    have middleLt : middle.clock < source.clock :=
      Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock body entry bodyResult middle bodyRun) entryLt
    cases bodyResult with
    | none => rfl
    | some value =>
      cases value with
      | result value =>
        dsimp only at run
        by_cases correct : value = .loc l1 l2
        · simp only [selectedContinuationBudget, correct, ↓reduceIte]
          rw [if_neg (not_not_intro correct)] at run
          rw [ih rp middle middleLt post result run notTimeout extra]
        · simp only [selectedContinuationBudget, correct, ↓reduceIte]
          rfl
      | exception value =>
        cases handler with
        | none => rfl
        | some packet =>
          rcases packet with ⟨hp, hs, hl⟩
          by_cases correct : value = .loc hs hl
          · simp only [selectedContinuationBudget, correct, ↓reduceIte]
            dsimp only at run
            rw [if_neg (not_not_intro correct)] at run
            rw [ih hp middle middleLt post result run notTimeout extra]
          · simp only [selectedContinuationBudget, correct, ↓reduceIte]
            rfl
      | «break» _ | «continue» _ | halt _ | error | finalFFI _ | timeOut => rfl

#print axioms stackCost_addClock_return
end InitECandidate.Runtime.StackToLab
