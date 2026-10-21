import InitECandidate.Runtime.StackRemoveAddressCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem nativeCost_memory {F : Type} (gap register : Nat) (op : WordMemOp) (address : HolAddr 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (.inst (.mem op register address)) source = 1 + gap := by
  simp [stackExecutionCost, nativePriceWithGap, instLocalCost]

/-- A large stack load adjusts its address once, then performs one load. -/
theorem nativeCost_stackLoad {F : Type} (gap register count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.stackLoad register count) source ≤ (count / 255 + 2) * (1 + gap) := by
  unfold StackRemove.stackLoad
  have bound := nativeCost_seq_le gap _ _ ((count / 255 + 1) * (1 + gap)) (1 + gap)
    (fun s => nativeCost_upshift gap register count s)
    (fun s => (nativeCost_memory gap register .load (.addr register 0) s).le) source
  simpa only [Nat.add_mul, Nat.one_mul, Nat.succ_mul, Nat.add_assoc] using bound

/-- A large stack store restores its address register, so charges both
adjustment sequences and the actual store. -/
theorem nativeCost_stackStore {F : Type} (gap address register count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.stackStore address register count) source ≤
      (count / 255 + 1) * (1 + gap) + (1 + gap) + (count / 255 + 1) * (1 + gap) := by
  unfold StackRemove.stackStore
  have tail (s : StackSemStateFiniteExact 64 LabToTarget.Config F) :=
    nativeCost_seq_le gap (.inst (.mem .store register (.addr address 0)))
      (StackRemove.downshift address count) (1 + gap) ((count / 255 + 1) * (1 + gap))
      (fun t => (nativeCost_memory gap register .store (.addr address 0) t).le)
      (fun t => nativeCost_downshift gap address count t) s
  have bound := nativeCost_seq_le gap (StackRemove.upshift address count) _
    ((count / 255 + 1) * (1 + gap)) ((1 + gap) + (count / 255 + 1) * (1 + gap))
    (fun s => nativeCost_upshift gap address count s) tail source
  simpa only [Nat.add_assoc] using bound

#print axioms nativeCost_memory
#print axioms nativeCost_stackLoad
#print axioms nativeCost_stackStore
end InitECandidate.Runtime.StackToLab
