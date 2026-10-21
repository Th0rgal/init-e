import InitECandidate.Runtime.StackExecutionTrace
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

private theorem ffi_code {F : Type} (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (result : Option (StackSemResult 64))
    (run : StackSemEvaluate.evaluate (.ffi name ptr len ptr2 len2 ret, source) = (result, post)) :
    post.code = source.code := by
  rw [StackSemEvaluate.evaluate_ffi] at run
  repeat' split at run
  all_goals obtain ⟨_, rfl⟩ := Prod.mk.inj run
  all_goals rfl

private theorem shared_code {F : Type} (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64) (result : Option (StackSemResult 64))
    (run : StackSemEvaluate.evaluate (.shMemOp op reg (.addr base offset), source) = (result, post)) :
    post.code = source.code := by
  rw [StackSemEvaluate.evaluate_shMemOp] at run
  split at run
  · split at run
    · obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl
    · exact (StackPropsSharedMemoryClock.shMemOpConst _ _ _ _ _ _ run).2.2.2.2.1
  · obtain ⟨_, rfl⟩ := Prod.mk.inj run; rfl

/-- Supported leaf operations preserve the source code map on their actual run. -/
theorem ExecutionLeaf.code_eq {F : Type} {source post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {p : HolProg 64} {kind : ExecutionKind} (leaf : ExecutionLeaf source p kind)
    (run : StackSemEvaluate.evaluate (p, source) = (kind.result, post)) : post.code = source.code := by
  cases leaf with
  | skip =>
    rw [StackSemEvaluate.evaluate_skip] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | inst instruction =>
    rw [StackSemEvaluate.evaluate_inst] at run
    cases h : StackSemInst.instHOL instruction source with
    | none => simp [h, ExecutionKind.result] at run
    | some next =>
      rw [h] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact (StackPropsInstructionConstants.instConst _ _ _ h).2.2.2.2.2.1
  | location reg sid lid =>
    rw [StackSemEvaluate.evaluate_locValue] at run
    split at run <;> obtain ⟨_, rfl⟩ := Prod.mk.inj run <;> rfl
  | tick =>
    rw [StackSemEvaluate.evaluate_tick] at run
    split at run <;> obtain ⟨_, rfl⟩ := Prod.mk.inj run <;> rfl
  | halt reg value read =>
    rw [StackSemEvaluate.evaluate_halt, read] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | breakCase index =>
    rw [StackSemEvaluate.evaluate_break] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | continueCase index =>
    rw [StackSemEvaluate.evaluate_continue] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | returnCase reg sid lid read valid =>
    rw [StackSemEvaluate.evaluate_ret, read] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | raiseCase reg sid lid read valid =>
    rw [StackSemEvaluate.evaluate_raise, read] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | ffiNormal name ptr len ptr2 len2 ret => exact ffi_code source post name ptr len ptr2 len2 ret _ run
  | ffiFinal name ptr len ptr2 len2 ret event => exact ffi_code source post name ptr len ptr2 len2 ret _ run
  | sharedNormal op reg base offset => exact shared_code source post op reg base offset _ run
  | sharedFinal op reg base offset event => exact shared_code source post op reg base offset _ run

/-- Code-map preservation follows through the whole semantic derivation,
including calls and host responses, without a global state oracle. -/
theorem ExecutionTrace.code_eq {F : Type} {source post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {p : HolProg 64} {kind : ExecutionKind} (trace : ExecutionTrace source p kind post) : post.code = source.code := by
  induction trace with
  | leaf run classification => exact classification.code_eq run
  | seqNext run firstTree secondTree ihFirst ihSecond => exact ihSecond.trans ihFirst
  | seqStop run nonNormal firstTree ih => exact ih
  | branch x y choice run lhs rhs chosen selectedTree ih => exact ih
  | loopBreak run bodyTree ih => exact ih
  | loopStep run bodyTree clock restTree ihBody ihRest => exact ihRest.trans ihBody
  | loopContinue run bodyTree clock restTree ihBody ihRest => exact ihRest.trans ihBody
  | loopExit run bodyTree stopped exited ih => exact ih
  | loopFinal run bodyTree stopped exited ih => exact ih
  | callTail run positive found nonNormal bodyTree ih => exact ih
  | rawCall run positive found nonNormal bodyTree ih => exact ih
  | jumpFalse x y run readX readY chosen =>
    rw [StackSemEvaluate.evaluate_jumpLower, readX, readY] at run
    simp only [chosen, Bool.false_eq_true, if_false] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  | jumpTrue x y run positive readX readY chosen found nonNormal bodyTree ih => exact ih
  | callReturn run positive found bodyTree returnTree ihBody ihReturn => exact ihReturn.trans ihBody
  | callHandler run positive found bodyTree handlerTree ihBody ihHandler => exact ihHandler.trans ihBody
  | callExit run positive found propagates bodyTree ih => exact ih
  | callFinal run positive found propagates bodyTree ih => exact ih

#print axioms ExecutionLeaf.code_eq
#print axioms ExecutionTrace.code_eq
end InitECandidate.Runtime.StackToLab
