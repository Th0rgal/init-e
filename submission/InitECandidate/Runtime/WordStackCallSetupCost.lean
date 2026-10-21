import InitECandidate.Runtime.WordStackCallFrameCost
import InitECandidate.Runtime.WordStackLiteralCost
import Flapjack.Compiler.Backend.WordToStack.NativeLive
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Saving a nonempty caller frame pays one literal and one small-offset store. -/
theorem wordStack_live_cost {F : Type} (live : Spt Unit × Spt Unit)
    (bitmaps : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wLiveNative live bitmaps kf).1 source ≤ 19 := by
  unfold wLiveNative
  split
  · simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  · apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 12 7 rfl
    · intro state
      have bound := const_native_length_le kf.1
        (BitVec.ofNat 64 ((Flapjack.Compiler.Backend.WordToStack.insertBitmap (Flapjack.Compiler.Backend.WordToStack.writeBitmapExact live.2 kf.1 kf.2.2) bitmaps).2 + 1))
      simpa only [stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
        using Nat.add_le_add_right bound 6
    · intro state
      simp only [stackExecutionCost, riscv_stack_store_price kf.1 0 (by omega), Nat.le_refl]

/-- Restoring the handler costs 21, followed by precisely the supplied
continuation budget; an early stop can only discard continuation work. -/
theorem wordStack_popHandler_cost {F : Type} {β γ : Type}
    (kf : Nat × β × γ) (body : HolProg 64) (budget : Nat)
    (bodyBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) body s ≤ budget)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (popHandlerNative false kf body) source ≤ 21 + budget := by
  unfold popHandlerNative
  have freeBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots false)) body) s ≤ 7 + budget := by
    intro s
    apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 budget rfl _ bodyBound s
    intro state
    simpa only [stackExecutionCost] using guest_frame_free_price
      (Flapjack.Compiler.Backend.WordToStack.handlerSlots false) (by decide)
  have setBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.seq (.set .handler kf.1)
          (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots false)) body)) s ≤ 14 + budget := by
    intro s
    have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) (.set .handler kf.1)
      (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots false)) body) 7 (7+budget) rfl
      (fun state => by simp only [stackExecutionCost, removalLocalPrice, Nat.le_refl]) freeBound s
    omega
  have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) (.stackLoad kf.1 2)
    (.seq (.set .handler kf.1) (.seq (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots false)) body)) 7 (14+budget) rfl
    (fun state => by simp only [stackExecutionCost, riscv_stack_load_price kf.1 2 (by omega), Nat.le_refl]) setBound source
  omega

#print axioms wordStack_live_cost
#print axioms wordStack_popHandler_cost
end InitECandidate.Runtime.WordToStack
