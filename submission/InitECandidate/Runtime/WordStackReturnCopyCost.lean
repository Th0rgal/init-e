import InitECandidate.Runtime.WordStackCallFrameCost
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Each executed return-slot copy pays one small-offset load and store. -/
theorem wordStack_copyRetAux_cost {F : Type} (k f n : Nat) (fits : n+f ≤ 256)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (copyRetAuxNative k f n) source ≤ 14*n := by
  induction n generalizing source with
  | zero => simp [copyRetAuxNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  | succ n ih =>
    have tail : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (.seq (.stackStore k (n+f)) (copyRetAuxNative k f n)) s ≤ 7+14*n := by
      intro s
      apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
        (.stackStore k (n+f)) (copyRetAuxNative k f n) 7 (14*n) rfl _ (ih (by omega)) s
      intro state
      simp only [stackExecutionCost, riscv_stack_store_price k (n+f) (by omega), Nat.le_refl]
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
      (.stackLoad k n) (.seq (.stackStore k (n+f)) (copyRetAuxNative k f n))
      7 (7+14*n) rfl
      (fun state => by simp only [stackExecutionCost, riscv_stack_load_price k n (by omega), Nat.le_refl]) tail source
    simp only [copyRetAuxNative, listSeq]
    omega

/-- A nonempty return block costs at most 21 per spilled word, including
freeing its temporary slots. Zero spilled returns incur no extra work. -/
theorem wordStack_copyRet_cost {F β γ : Type} (isHandle : Bool)
    (kf : Nat × Nat × γ) (values : List β) (body : HolProg 64) (budget : Nat)
    (frameSmall : kf.2.1 ≤ 92)
    (returnsSmall : Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values ≤ 92)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (copyRetNative false isHandle kf values body) source ≤
      21 * Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values + budget := by
  let n := Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 values
  unfold copyRetNative
  change stackExecutionCost _ (if n=0 then body else _) source ≤ 21*n+budget
  split
  · rename_i zero
    simpa only [zero, Nat.mul_zero, Nat.zero_add] using bodyBound source
  · rename_i nonzero
    have free : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (seqStackFreeNative n body) s ≤ 7*n+budget := by
      intro s
      have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
        (.stackFree n) body 7 budget rfl
        (fun state => by simpa only [stackExecutionCost] using guest_frame_free_price n returnsSmall) bodyBound s
      simpa only [seqStackFreeNative, if_neg nonzero] using
        (bound.trans (by omega))
    have copies : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
        stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
          (copyRetAuxNative kf.1 (if isHandle then kf.2.1 + Flapjack.Compiler.Backend.WordToStack.handlerSlots false else kf.2.1) n) s ≤ 14*n := by
      intro s
      apply wordStack_copyRetAux_cost
      cases isHandle <;> simp only [Bool.false_eq_true, ↓reduceIte, Flapjack.Compiler.Backend.WordToStack.handlerSlots] <;> omega
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
      (copyRetAuxNative kf.1 (if isHandle then kf.2.1 + Flapjack.Compiler.Backend.WordToStack.handlerSlots false else kf.2.1) n)
      (seqStackFreeNative n body) (14*n) (7*n+budget) rfl copies free source
    dsimp only [n] at bound
    omega

#print axioms wordStack_copyRetAux_cost
#print axioms wordStack_copyRet_cost
end InitECandidate.Runtime.WordToStack
