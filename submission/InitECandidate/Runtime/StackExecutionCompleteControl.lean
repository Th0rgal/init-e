import InitECandidate.Runtime.StackExecutionAtomicComplete
import InitECandidate.Runtime.StackExecutionCodePreservation
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Completeness at an actual source state. All premises are source semantic
or static eligibility facts; no native cost or assumed trace is supplied. -/
def ExecutionCompleteAt {F : Type} (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ result post, StackSemEvaluate.evaluate (p, source) = (result, post) →
    ExecutionResultValid source.code result → executionSupported p = true →
    ExecutionCodeSupported source.code → ExecutionLabelScope source.code p →
    ExecutionTrace source p (executionKindOfResult result) post

def ExecutionCompleteIH {F : Type} (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ (q : HolProg 64) (child : StackSemStateFiniteExact 64 LabToTarget.Config F), StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) →
    ExecutionCompleteAt q child

private theorem smaller {F : Type} (p q : HolProg 64)
    (source child : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (clock : child.clock ≤ source.clock) (size : sizeOf q < sizeOf p) :
    StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) := by
  rcases Nat.lt_or_eq_of_le clock with lt | eq
  · exact Prod.Lex.left _ _ lt
  · rw [eq]; exact Prod.Lex.right _ size

theorem executionKindOfResult_nonNormal (result : StackSemResult 64) :
    executionKindOfResult (some result) ≠ .normal := by
  cases result <;> try (intro h; cases h)
  rename_i value
  cases value <;> intro h <;> cases h

/-- Sequence completeness exposes only the actually reached suffix. -/
theorem executionComplete_seq {F : Type} (first second : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.seq first second) source) :
    ExecutionCompleteAt (.seq first second) source := by
  intro result post run valid supported global scope
  have rootRun := run
  obtain ⟨firstSupported, secondSupported⟩ := executionSupported_seq.1 supported
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  rw [firstRun] at run
  have firstSmaller := smaller (.seq first second) first source source (Nat.le_refl _) (by simp; omega)
  cases firstResult with
  | none =>
    have firstTree := ih first source firstSmaller none middle firstRun True.intro firstSupported global scope.seq_left
    have secondSmaller := smaller (.seq first second) second source middle
      (StackSemEvaluateClock.evaluateClock first source none middle firstRun) (by simp)
    have secondValid : ExecutionResultValid middle.code result := by rw [firstTree.code_eq]; exact valid
    have secondGlobal : ExecutionCodeSupported middle.code := by rw [firstTree.code_eq]; exact global
    have secondScope : ExecutionLabelScope middle.code second := by rw [firstTree.code_eq]; exact scope.seq_right
    have secondTree := ih second middle secondSmaller result post run secondValid secondSupported secondGlobal secondScope
    exact ExecutionTrace.seqNext (by simpa only [executionKindOfResult_result] using rootRun) firstTree secondTree
  | some value =>
    have pairs := Prod.mk.inj run
    obtain ⟨rfl, rfl⟩ := pairs
    have firstTree := ih first source firstSmaller (some value) middle firstRun valid firstSupported global scope.seq_left
    exact ExecutionTrace.seqStop (by simpa only [executionKindOfResult_result] using rootRun)
      (executionKindOfResult_nonNormal value) firstTree

/-- Conditional completeness follows the actual operands and comparison. -/
theorem executionComplete_ite {F : Type} (yes no : HolProg 64)
    (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.ite cmp reg operand yes no) source) :
    ExecutionCompleteAt (.ite cmp reg operand yes no) source := by
  intro result post run valid supported global scope
  have rootRun := run
  obtain ⟨yesSupported, noSupported⟩ := executionSupported_ite.1 supported
  rw [StackSemEvaluate.evaluate_ite] at run
  cases lhs : StackSemStateOps.getVar reg source with
  | none =>
    simp only [lhs] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid
  | some x =>
    cases rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      simp only [lhs, rhs] at run
      obtain ⟨rfl, _⟩ := Prod.mk.inj run
      exact False.elim valid
    | some y =>
      simp only [lhs, rhs] at run
      cases chosen : wordSemWordCmp cmp x y with
      | none =>
        rw [chosen] at run
        obtain ⟨rfl, _⟩ := Prod.mk.inj run
        exact False.elim valid
      | some choice =>
        rw [chosen] at run
        have selectedRun : StackSemEvaluate.evaluate ((if choice then yes else no), source) = (result, post) := by
          cases choice <;> exact run
        have selectedSupported : executionSupported (if choice then yes else no) = true := by
          cases choice <;> assumption
        have selectedScope : ExecutionLabelScope source.code (if choice then yes else no) := by
          cases choice
          · exact scope.ite_right
          · exact scope.ite_left
        have selectedSmaller := smaller (.ite cmp reg operand yes no) (if choice then yes else no)
          source source (Nat.le_refl _) (by cases choice <;> simp <;> omega)
        have selectedTree := ih _ source selectedSmaller result post selectedRun valid selectedSupported global selectedScope
        exact ExecutionTrace.branch x y choice (by simpa only [executionKindOfResult_result] using rootRun)
          lhs rhs chosen selectedTree

#print axioms executionComplete_seq
#print axioms executionComplete_ite
end InitECandidate.Runtime.StackToLab
