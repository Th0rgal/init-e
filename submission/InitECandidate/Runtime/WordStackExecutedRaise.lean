import InitECandidate.Runtime.WordStackExecutedReturn
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Raise
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Unwinding uses the saved handler pointer directly. Its cost is constant
in the number of skipped source frames. -/
theorem wordStack_raise_stub_cost {F : Type} (k : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (raiseStubNative false k) source ≤ 61 := by
  have getBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.get k .handler) s ≤ 7 := by
    intro s; simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  have sizeBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.stackSetSize k) s ≤ 25 := by
    intro s; simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  have loadBound : ∀ count, count ≤ 91 → ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.stackLoad k count) s ≤ 7 := by
    intro count small s
    simp only [stackExecutionCost, guest_spill_load_price k count small, Nat.le_refl]
  have setBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) (.set .handler k) s ≤ 7 := by
    intro s; simp [stackExecutionCost, removalLocalPrice]
  have freeBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        (.stackFree (Flapjack.Compiler.Backend.WordToStack.handlerSlots false)) s ≤ 7 := by
    intro s
    simp only [stackExecutionCost]
    exact guest_frame_free_price _ (by decide)
  unfold raiseStubNative
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 54 rfl getBound (fun s => ?_) source
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 25 29 rfl sizeBound (fun s => ?_) s
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 0 29 rfl
    (fun state => by simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]) (fun s => ?_) s
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 22 rfl (loadBound 2 (by decide)) (fun s => ?_) s
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 15 rfl setBound (fun s => ?_) s
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 8 rfl (loadBound 1 (by decide)) (fun s => ?_) s
  apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 1 rfl freeBound (fun s => ?_) s
  simp [stackExecutionCost, removalLocalPrice, nativePriceWithGap]

theorem executedSimulation_raise {F : Type} (ac : AsmConfigExact 64) (name : Nat)
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.raise name) source 63 := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  obtain ⟨clock, final, output, run, related⟩ := Raise.compCorrectRaise ac name source
    k f frame post target result bs bsPost n nPost compiled lens premises
  refine ⟨clock, final, output, run, related, ?_⟩
  intro actualRegisters
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  rw [← programEq]
  have stub : sptLookup raiseStubLocation target.code = some (raiseStubNative false k) := by
    have full := premises.2.2.1
    simp only [stateRel] at full
    tauto
  rw [stackExecutionCost.eq_6]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  split
  · change 2 ≤ 63; decide
  · simp only [StackSemControl.findCode, stub]
    change 2 + stackExecutionCost _ (raiseStubNative false k) _ ≤ 63
    exact Nat.add_le_add_left (wordStack_raise_stub_cost k _) 2

#print axioms wordStack_raise_stub_cost
#print axioms executedSimulation_raise
end InitECandidate.Runtime.WordToStack
