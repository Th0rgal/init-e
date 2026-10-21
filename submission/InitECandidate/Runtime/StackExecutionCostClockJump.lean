import InitECandidate.Runtime.StackExecutionCostClockReturn
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem stackCost_addClock_jump {F : Type} (price : HolProg 64 → Nat) (regX regY dest : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      child.clock < source.clock → CostClockStableAt price q child) :
    CostClockStableAt price (.jumpLower regX regY dest) source := by
  intro post result run notTimeout extra
  rw [stackExecutionCost.eq_4 (fun p _ => price p) {source with clock := source.clock + extra} regX regY dest,
    stackExecutionCost.eq_4 (fun p _ => price p) source regX regY dest]
  have read (reg : Nat) : StackSemStateOps.getVar reg {source with clock := source.clock + extra} =
      StackSemStateOps.getVar reg source := by simp [StackSemStateOps.getVar]
  rw [read regX, read regY]
  rw [StackSemEvaluate.evaluate_jumpLower] at run
  cases readX : StackSemStateOps.getVar regX source with
  | none => simp only [readX]
  | some x =>
    cases x with
    | loc _ _ => simp only [readX]
    | word x =>
      cases readY : StackSemStateOps.getVar regY source with
      | none => simp only [readX, readY]
      | some y =>
        cases y with
        | loc _ _ => simp only [readX, readY]
        | word y =>
          simp only [readX, readY] at run ⊢
          cases chosen : wordCmpHOL .lower x y with
          | false => simp only [chosen, Bool.false_eq_true, ↓reduceIte]
          | true =>
            simp only [chosen, ↓reduceIte] at run ⊢
            cases found : sptLookup dest source.code with
            | none =>
              simp only [StackSemControl.findCode, found]
              split <;> split <;> rfl
            | some body =>
              simp only [StackSemControl.findCode, found] at run
              have positive : source.clock ≠ 0 := by
                intro zero
                rw [if_pos zero] at run
                exact notTimeout (Prod.mk.inj run).1.symm
              have shiftedPositive : source.clock + extra ≠ 0 := by omega
              simp only [positive, shiftedPositive, ↓reduceIte, StackSemControl.findCode, found]
              rw [if_neg positive] at run
              rcases bodyRun : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) with ⟨bodyResult, middle⟩
              rw [bodyRun] at run
              have bodyNotTimeout : bodyResult ≠ some .timeOut := by
                intro eq
                rw [eq] at run
                simp only [StackSemControl.badFunReturn, Bool.false_eq_true, ↓reduceIte] at run
                exact notTimeout (Prod.mk.inj run).1.symm
              have smaller : (StackSemStateOps.decClock source).clock < source.clock := by
                change source.clock - 1 < source.clock
                omega
              rw [StackProps.EvaluateAddClock.decClock_addClock source extra positive,
                ih body _ smaller middle bodyResult bodyRun bodyNotTimeout extra]

#print axioms stackCost_addClock_jump
end InitECandidate.Runtime.StackToLab
