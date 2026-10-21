import InitECandidate.Runtime.StackCostSeqAssoc
import InitECandidate.Runtime.WordStackReturnCopyCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab
variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

theorem stackCost_seq_skip_left {F : Type} (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p) (.seq .skip body) source =
      stackExecutionCost (fun p _ => price p) body source := by
  rw [stackExecutionCost_seq]
  simp only [ConservativeRemovalPrice.freeSeq (price := price), stackExecutionCost,
    ConservativeRemovalPrice.skip (price := price), StackSemEvaluate.evaluate_skip, Nat.zero_add]

/-- Counter counterpart of the original handler-pop continuation factoring. -/
theorem stackCost_popHandler_sequence {F β γ : Type} (kf : Nat × β × γ) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p) (popHandlerNative false kf body) source =
      stackExecutionCost (fun p _ => price p) (.seq (popHandlerNative false kf .skip) body) source := by
  unfold popHandlerNative
  rw [stackCost_seq_assoc]
  apply stackCost_seq_congr_right (price := price)
  intro afterLoad
  rw [stackCost_seq_assoc]
  apply stackCost_seq_congr_right (price := price)
  intro afterSet
  rw [stackCost_seq_assoc]
  exact stackCost_seq_congr_right (price := price) _ _ _
    (fun state => (stackCost_seq_skip_left (price := price) body state).symm) afterSet

/-- Counter factoring of copy_ret plus handler-pop; early exits retain exactly
which restoration statements were reached. -/
theorem stackCost_handler_restore_sequence {F β : Type} (k frame payload : Nat)
    (values : List β) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p)
      (copyRetNative false true (k,frame,payload) values (popHandlerNative false (k,frame,payload) body)) source =
    stackExecutionCost (fun p _ => price p)
      (.seq (copyRetNative false true (k,frame,payload) values (popHandlerNative false (k,frame,payload) .skip)) body) source := by
  by_cases zero : Compiler.Backend.WordToStack.numStackRet k values = 0
  · simp only [copyRetNative,zero,if_true]
    exact stackCost_popHandler_sequence _ body source
  · simp only [copyRetNative,zero,if_false,seqStackFreeNative,
      Compiler.Backend.WordToStack.handlerSlots,Bool.false_eq_true,if_true]
    rw [stackCost_seq_assoc]
    apply stackCost_seq_congr_right (price := price)
    intro afterCopy
    rw [stackCost_seq_assoc]
    exact stackCost_seq_congr_right (price := price) _ _ _
      (fun state => stackCost_popHandler_sequence (price := price) _ body state) afterCopy

/-- Concrete local restoration cost, reused at the actual restored state by
normal-return composition. -/
theorem wordStack_handler_restore_prefix_cost {F β : Type} (k frame payload : Nat)
    (values : List β) (frameSmall : frame ≤ 92)
    (returnsSmall : Compiler.Backend.WordToStack.numStackRet k values ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p)
      (copyRetNative false true (k,frame,payload) values (popHandlerNative false (k,frame,payload) .skip)) source ≤
      21*Compiler.Backend.WordToStack.numStackRet k values + 21 := by
  apply (ConservativeRemovalPrice.execution (price := price) _ source).trans
  apply wordStack_copyRet_cost true (k,frame,payload) values _ 21 frameSmall returnsSmall
  intro state
  exact wordStack_popHandler_cost (k,frame,payload) .skip 0
    (fun s => by simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]) state

#print axioms stackCost_seq_skip_left
#print axioms stackCost_popHandler_sequence
#print axioms stackCost_handler_restore_sequence
#print axioms wordStack_handler_restore_prefix_cost
end InitECandidate.Runtime.WordToStack
