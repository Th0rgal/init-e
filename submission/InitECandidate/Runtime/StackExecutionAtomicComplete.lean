import InitECandidate.Runtime.StackExecutionEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

private theorem shared_helper_class {F : Type} (op : HolMemop) (reg : Nat) (address : BitVec 64)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) (result : Option (StackSemResult 64))
    (run : StackSemShMem.shMemOp op reg address source = (result, post)) :
    result = none ∨ result = some .error ∨ ∃ event, result = some (.finalFFI event) := by
  cases op <;> simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
    StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte, StackSemShMem.shMemLoad16,
    StackSemShMem.shMemStore16, StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32] at run
  all_goals repeat' split at run
  all_goals obtain ⟨rfl, _⟩ := Prod.mk.inj run
  all_goals simp

private theorem shared_eval_class {F : Type} (op : HolMemop) (reg base : Nat) (offset : BitVec 64)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) (result : Option (StackSemResult 64))
    (run : StackSemEvaluate.evaluate (.shMemOp op reg (.addr base offset), source) = (result, post))
    (valid : ExecutionResultValid source.code result) : result = none ∨ ∃ event, result = some (.finalFFI event) := by
  rw [StackSemEvaluate.evaluate_shMemOp] at run
  split at run
  · split at run
    · obtain ⟨rfl, _⟩ := Prod.mk.inj run
      exact False.elim valid
    · rcases shared_helper_class _ _ _ _ _ _ run with normal | error | final
      · exact Or.inl normal
      · exact False.elim (valid.nonerror error)
      · exact Or.inr final
  · obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid

/-- Every successful valid atomic evaluation supplies a semantic derivation.
There is no assumed derivation or target budget in the premises. -/
theorem executionTrace_atomic {F : Type}
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) (p : HolProg 64)
    (result : Option (StackSemResult 64)) (atomic : executionAtomic p = true)
    (run : StackSemEvaluate.evaluate (p, source) = (result, post))
    (valid : ExecutionResultValid source.code result) :
    ExecutionTrace source p (executionKindOfResult result) post := by
  apply ExecutionTrace.leaf ?_ ?_
  · simpa only [executionKindOfResult_result] using run
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  case skip =>
    rw [StackSemEvaluate.evaluate_skip] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact .skip
  case inst instruction =>
    rw [StackSemEvaluate.evaluate_inst] at run
    split at run
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    · exact .inst instruction
    · exact False.elim valid
  case locValue reg sid lid =>
    rw [StackSemEvaluate.evaluate_locValue] at run
    split at run
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    · exact .location reg sid lid
    · exact False.elim valid
  case tick =>
    rw [StackSemEvaluate.evaluate_tick] at run
    split at run
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    · exact False.elim valid
    · exact .tick
  case halt reg =>
    rw [StackSemEvaluate.evaluate_halt] at run
    cases read : StackSemStateOps.getVar reg source with
    | none =>
      rw [read] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact False.elim valid
    | some value =>
      rw [read] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      cases value with
      | word value => exact .halt reg value read
      | loc sid lid => exact False.elim valid
  case ret reg =>
    rw [StackSemEvaluate.evaluate_ret] at run
    cases read : StackSemStateOps.getVar reg source with
    | none =>
      rw [read] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact False.elim valid
    | some value =>
      cases value with
      | word value =>
        rw [read] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
        exact False.elim valid
      | loc sid lid =>
        rw [read] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
        exact .returnCase reg sid lid read valid
  case raise reg =>
    rw [StackSemEvaluate.evaluate_raise] at run
    cases read : StackSemStateOps.getVar reg source with
    | none =>
      rw [read] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact False.elim valid
    | some value =>
      cases value with
      | word value =>
        rw [read] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
        exact False.elim valid
      | loc sid lid =>
        rw [read] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
        exact .raiseCase reg sid lid read valid
  case «break» index =>
    rw [StackSemEvaluate.evaluate_break] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact .breakCase index
  case «continue» index =>
    rw [StackSemEvaluate.evaluate_continue] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact .continueCase index
  case ffi name ptr len ptr2 len2 ret =>
    rw [StackSemEvaluate.evaluate_ffi] at run
    repeat' split at run
    all_goals obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    all_goals first
      | exact .ffiNormal name ptr len ptr2 len2 ret
      | exact .ffiFinal name ptr len ptr2 len2 ret _
      | exact False.elim valid
  case shMemOp op reg address =>
    cases address with
    | addr base offset =>
      rcases shared_eval_class op reg base offset source post result run valid with normal | ⟨event, final⟩
      · subst result; exact .sharedNormal op reg base offset
      · subst result; exact .sharedFinal op reg base offset event

#print axioms executionTrace_atomic
end InitECandidate.Runtime.StackToLab
